// Copyright 2017 Google Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use rustc_span::source_map::{FileLoader, RealFileLoader};
use std::collections::HashMap;
use std::io;
use std::path::{Path, PathBuf};

#[derive(Clone)]
pub(crate) struct InMemoryFileLoader<T: FileLoader + Send + Sync> {
    files: HashMap<PathBuf, String>,
    inner_file_loader: T,
}

impl<T: FileLoader + Send + Sync> InMemoryFileLoader<T> {
    pub(crate) fn new(inner: T) -> InMemoryFileLoader<T> {
        InMemoryFileLoader {
            files: HashMap::new(),
            inner_file_loader: inner,
        }
    }

    pub(crate) fn add_file<P: Into<PathBuf>>(&mut self, file_name: P, contents: String) {
        self.files.insert(file_name.into(), contents);
    }
}

impl<T: FileLoader + Send + Sync> FileLoader for InMemoryFileLoader<T> {
    fn file_exists(&self, path: &Path) -> bool {
        self.files.contains_key(path) || self.inner_file_loader.file_exists(path)
    }

    fn abs_path(&self, _: &Path) -> Option<PathBuf> {
        None
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        if let Some(contents) = self.files.get(path) {
            return Ok(contents.to_string());
        }
        self.inner_file_loader.read_file(path)
    }
}

/// We only need this because `RealFileLoader` doesn't derive `Clone`
#[derive(Clone)]
pub(crate) struct ClonableRealFileLoader;

impl FileLoader for ClonableRealFileLoader {
    fn file_exists(&self, path: &Path) -> bool {
        RealFileLoader.file_exists(path)
    }

    fn abs_path(&self, path: &Path) -> Option<PathBuf> {
        RealFileLoader.abs_path(path)
    }

    fn read_file(&self, path: &Path) -> io::Result<String> {
        RealFileLoader.read_file(path)
    }
}
