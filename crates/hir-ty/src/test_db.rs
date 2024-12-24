//! Database used for testing `hir`.

use std::{fmt, hash::BuildHasherDefault, panic, sync::Mutex};

use base_db::{
    CrateId, FileSourceRootInput, FileText, RootQueryDb, SourceDatabase, SourceRoot, SourceRootId,
    SourceRootInput, Upcast,
};
use dashmap::{mapref::entry::Entry, DashMap};
use hir_def::{db::DefDatabase, ModuleId};
use hir_expand::db::ExpandDatabase;
use rustc_hash::{FxHashMap, FxHasher};
use salsa::{AsDynDatabase, Durability, Setter};
use span::{EditionedFileId, FileId};
use syntax::TextRange;
use test_utils::extract_annotations;
use triomphe::Arc;
use vfs::AnchoredPath;

#[salsa::db]
#[derive(Clone)]
pub(crate) struct TestDB {
    storage: salsa::Storage<Self>,
    files: Arc<DashMap<vfs::FileId, FileText, BuildHasherDefault<FxHasher>>>,
    source_roots: Arc<DashMap<SourceRootId, SourceRootInput, BuildHasherDefault<FxHasher>>>,
    file_source_roots: Arc<DashMap<vfs::FileId, FileSourceRootInput, BuildHasherDefault<FxHasher>>>,
    events: Arc<Mutex<Option<Vec<salsa::Event>>>>,
}

impl Default for TestDB {
    fn default() -> Self {
        let mut this = Self {
            storage: Default::default(),
            events: Default::default(),
            files: Default::default(),
            source_roots: Default::default(),
            file_source_roots: Default::default(),
        };
        this.set_expand_proc_attr_macros_with_durability(true, Durability::HIGH);
        this
    }
}

impl fmt::Debug for TestDB {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TestDB").finish()
    }
}

impl Upcast<dyn ExpandDatabase> for TestDB {
    fn upcast(&self) -> &(dyn ExpandDatabase + 'static) {
        self
    }
}

impl Upcast<dyn DefDatabase> for TestDB {
    fn upcast(&self) -> &(dyn DefDatabase + 'static) {
        self
    }
}

impl Upcast<dyn RootQueryDb> for TestDB {
    fn upcast(&self) -> &(dyn RootQueryDb + 'static) {
        self
    }
}

impl Upcast<dyn SourceDatabase> for TestDB {
    fn upcast(&self) -> &(dyn SourceDatabase + 'static) {
        self
    }
}

#[salsa::db]
impl SourceDatabase for TestDB {
    fn file_text(&self, file_id: vfs::FileId) -> FileText {
        *self.files.get(&file_id).expect("Unable to fetch file; this is a bug")
    }

    fn set_file_text(&mut self, file_id: vfs::FileId, text: &str) {
        let files = Arc::clone(&self.files);
        match files.entry(file_id) {
            Entry::Occupied(mut occupied) => {
                occupied.get_mut().set_text(self).to(Arc::from(text));
            }
            Entry::Vacant(vacant) => {
                let text = FileText::new(self, Arc::from(text));
                vacant.insert(text);
            }
        };
    }

    fn set_file_text_with_durability(
        &mut self,
        file_id: vfs::FileId,
        text: &str,
        durability: salsa::Durability,
    ) {
        self.files
            .insert(file_id, FileText::builder(Arc::from(text)).durability(durability).new(self));
    }

    fn file_source_root(&self, id: vfs::FileId) -> FileSourceRootInput {
        let file_source_root = self
            .file_source_roots
            .get(&id)
            .expect("Unable to fetch FileSourceRootInput; this is a bug");
        *file_source_root
    }

    fn set_file_source_root_with_durability(
        &mut self,
        id: vfs::FileId,
        source_root_id: SourceRootId,
        durability: Durability,
    ) {
        let input = FileSourceRootInput::builder(source_root_id).durability(durability).new(self);
        self.file_source_roots.insert(id, input);
    }

    /// Source root of the file.
    fn source_root(&self, source_root_id: SourceRootId) -> SourceRootInput {
        let source_root = self
            .source_roots
            .get(&source_root_id)
            .expect("Unable to fetch source root id; this is a bug");

        *source_root
    }

    fn set_source_root_with_durability(
        &mut self,
        source_root_id: SourceRootId,
        source_root: Arc<SourceRoot>,
        durability: salsa::Durability,
    ) {
        let input = SourceRootInput::builder(source_root).durability(durability).new(self);
        self.source_roots.insert(source_root_id, input);
    }

    fn resolve_path(&self, path: AnchoredPath<'_>) -> Option<FileId> {
        // FIXME: this *somehow* should be platform agnostic...
        let source_root = self.file_source_root(path.anchor);
        let source_root = self.source_root(source_root.source_root_id(self));
        source_root.source_root(self).resolve_path(path)
    }

    fn relevant_crates(&self, file_id: FileId) -> Arc<[CrateId]> {
        let _p = tracing::info_span!("relevant_crates").entered();

        let source_root = self.file_source_root(file_id);
        self.source_root_crates(source_root.source_root_id(self))
    }
}

#[salsa::db]
impl salsa::Database for TestDB {
    fn salsa_event(&self, event: &dyn std::ops::Fn() -> salsa::Event) {
        let mut events = self.events.lock().unwrap();
        if let Some(events) = &mut *events {
            events.push(event());
        }
    }
}

impl panic::RefUnwindSafe for TestDB {}

impl TestDB {
    pub(crate) fn module_for_file_opt(&self, file_id: impl Into<FileId>) -> Option<ModuleId> {
        let file_id = file_id.into();
        for &krate in self.relevant_crates(file_id).iter() {
            let crate_def_map = self.crate_def_map(krate);
            for (local_id, data) in crate_def_map.modules() {
                if data.origin.file_id().map(EditionedFileId::file_id) == Some(file_id) {
                    return Some(crate_def_map.module_id(local_id));
                }
            }
        }
        None
    }

    pub(crate) fn module_for_file(&self, file_id: impl Into<FileId>) -> ModuleId {
        self.module_for_file_opt(file_id.into()).unwrap()
    }

    pub(crate) fn extract_annotations(
        &self,
    ) -> FxHashMap<EditionedFileId, Vec<(TextRange, String)>> {
        let mut files = Vec::new();
        let crate_graph = self.crate_graph();
        for krate in crate_graph.iter() {
            let crate_def_map = self.crate_def_map(krate);
            for (module_id, _) in crate_def_map.modules() {
                let file_id = crate_def_map[module_id].origin.file_id();
                files.extend(file_id)
            }
        }
        files
            .into_iter()
            .filter_map(|file_id| {
                let text = self.file_text(file_id.file_id());
                let annotations = extract_annotations(&text.text(self));
                if annotations.is_empty() {
                    return None;
                }
                Some((file_id, annotations))
            })
            .collect()
    }
}

impl TestDB {
    pub(crate) fn log(&self, f: impl FnOnce()) -> Vec<salsa::Event> {
        *self.events.lock().unwrap() = Some(Vec::new());
        f();
        self.events.lock().unwrap().take().unwrap()
    }

    pub(crate) fn log_executed(&self, f: impl FnOnce()) -> Vec<String> {
        let events = self.log(f);
        events
            .into_iter()
            .filter_map(|e| match e.kind {
                // This is pretty horrible, but `Debug` is the only way to inspect
                // QueryDescriptor at the moment.
                salsa::EventKind::WillExecute { database_key } => {
                    let ingredient = self
                        .as_dyn_database()
                        .ingredient_debug_name(database_key.ingredient_index());
                    Some(ingredient.to_string())
                }
                _ => None,
            })
            .collect()
    }
}
