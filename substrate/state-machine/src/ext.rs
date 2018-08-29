// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Conrete externalities implementation.

use std::{error, fmt, cmp::Ord};
use backend::Backend;
use changes_trie::{Storage as ChangesTrieStorage, compute_changes_trie_root, Configuration as ChangesTrieConfig};
use {Externalities, OverlayedChanges};
use hashdb::Hasher;
use memorydb::MemoryDB;
use rlp::Encodable;
use patricia_trie::{NodeCodec, TrieDBMut, TrieMut};
use heapsize::HeapSizeOf;

const EXT_NOT_ALLOWED_TO_FAIL: &'static str = "Externalities not allowed to fail within runtime";

/// Errors that can occur when interacting with the externalities.
#[derive(Debug, Copy, Clone)]
pub enum Error<B, E> {
	/// Failure to load state data from the backend.
	#[allow(unused)]
	Backend(B),
	/// Failure to execute a function.
	#[allow(unused)]
	Executor(E),
}

impl<B: fmt::Display, E: fmt::Display> fmt::Display for Error<B, E> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Error::Backend(ref e) => write!(f, "Storage backend error: {}", e),
			Error::Executor(ref e) => write!(f, "Sub-call execution error: {}", e),
		}
	}
}

impl<B: error::Error, E: error::Error> error::Error for Error<B, E> {
	fn description(&self) -> &str {
		match *self {
			Error::Backend(..) => "backend error",
			Error::Executor(..) => "executor error",
		}
	}
}

/// Wraps a read-only backend, call executor, and current overlayed changes.
pub struct Ext<'a, H, C, B, T>
where
	H: Hasher,
	C: NodeCodec<H>,
	B: 'a + Backend<H, C>,
	T: 'a + ChangesTrieStorage<H>,
{
	// The overlayed changes to write to.
	overlay: &'a mut OverlayedChanges,
	// The storage backend to read from.
	backend: &'a B,
	// The storage transaction necessary to commit to the backend.
	storage_transaction: Option<(B::Transaction, H::Out)>,
	// Changes trie storage to read from.
	changes_trie_storage: Option<&'a T>,
	// The changes trie transaction necessary to commit to the changes trie backend.
	changes_trie_transaction: Option<Option<(MemoryDB<H>, H::Out)>>,
}

impl<'a, H, C, B, T> Ext<'a, H, C, B, T>
where
	H: Hasher,
	C: NodeCodec<H>,
	B: 'a + Backend<H, C>,
	T: 'a + ChangesTrieStorage<H>,
	H::Out: Ord + Encodable + HeapSizeOf,
{
	/// Create a new `Ext` from overlayed changes and read-only backend
	pub fn new(overlay: &'a mut OverlayedChanges, backend: &'a B, changes_trie_storage: Option<&'a T>) -> Self {
		Ext {
			overlay,
			backend,
			storage_transaction: None,
			changes_trie_storage,
			changes_trie_transaction: None,
		}
	}

	/// Get the transaction necessary to update the backend.
	pub fn transaction(mut self) -> (B::Transaction, Option<MemoryDB<H>>) {
		let _ = self.storage_root();
		let _ = self.storage_changes_root();

		let (storage_transaction, changes_trie_transaction) = (
			self.storage_transaction
				.expect("storage_transaction always set after calling storage root; qed"),
			self.changes_trie_transaction
				.expect("changes_trie_transaction always set after calling storage changes root; qed")
				.map(|(tx, _)| tx),
		);

		(
			storage_transaction.0,
			changes_trie_transaction,
		)
	}

	/// Invalidates the currently cached storage root and the db transaction.
	///
	/// Called when there are changes that likely will invalidate the storage root.
	fn mark_dirty(&mut self) {
		self.storage_transaction = None;
		self.changes_trie_transaction = None;
	}
}

#[cfg(test)]
impl<'a, H, C, B, T> Ext<'a, H, C, B, T>
where
	H: Hasher,
	C: NodeCodec<H>,
	B: 'a + Backend<H,C>,
	T: 'a + ChangesTrieStorage<H>,
{
	pub fn storage_pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		use std::collections::HashMap;

		self.backend.pairs().iter()
			.map(|&(ref k, ref v)| (k.to_vec(), Some(v.to_vec())))
			.chain(self.overlay.committed.clone().into_iter().map(|(k, (v, _))| (k, v)))
			.chain(self.overlay.prospective.clone().into_iter().map(|(k, (v, _))| (k, v)))
			.collect::<HashMap<_, _>>()
			.into_iter()
			.filter_map(|(k, maybe_val)| maybe_val.map(|val| (k, val)))
			.collect()
	}
}

impl<'a, B: 'a, T: 'a, H, C> Externalities<H> for Ext<'a, H, C, B, T>
where
	H: Hasher,
	C: NodeCodec<H>,
	B: 'a + Backend<H, C>,
	T: 'a + ChangesTrieStorage<H>,
	H::Out: Ord + Encodable + HeapSizeOf,
{
	fn set_changes_trie_config(&mut self, block: u64, digest_interval: u64, digest_levels: u8) {
		self.overlay.set_changes_trie_config(block, ChangesTrieConfig {
			digest_interval,
			digest_levels,
		});
	}

	fn bind_to_extrinsic(&mut self, extrinsic_index: u32) {
		self.overlay.set_extrinsic_index(extrinsic_index);
	}

	fn storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.overlay.storage(key).map(|x| x.map(|x| x.to_vec())).unwrap_or_else(||
			self.backend.storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL))
	}

	fn exists_storage(&self, key: &[u8]) -> bool {
		match self.overlay.storage(key) {
			Some(x) => x.is_some(),
			_ => self.backend.exists_storage(key).expect(EXT_NOT_ALLOWED_TO_FAIL),
		}
	}

	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>) {
		self.mark_dirty();
		self.overlay.set_storage(key, value);
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		self.mark_dirty();
		self.overlay.clear_prefix(prefix);
		self.backend.for_keys_with_prefix(prefix, |key| {
			self.overlay.set_storage(key.to_vec(), None);
		});
	}

	fn chain_id(&self) -> u64 {
		42
	}

	fn storage_root(&mut self) -> H::Out {
		if let Some((_, ref root)) =  self.storage_transaction {
			return root.clone();
		}

		// compute and memoize
		let delta = self.overlay.committed.iter().map(|(k, (v, _))| (k, v))
			.chain(self.overlay.prospective.iter().map(|(k, (v, _))| (k, v)))
			.map(|(k, v)| (k.clone(), v.clone()));

		let (root, transaction) = self.backend.storage_root(delta);
		self.storage_transaction = Some((transaction, root));
		root
	}

	fn storage_changes_root(&mut self) -> Option<H::Out> {
		if let Some(ref changes_trie_transaction) = self.changes_trie_transaction {
			return changes_trie_transaction.as_ref().map(|t| t.1.clone());
		}

		let root_and_tx = compute_changes_trie_root::<_, T, H, C>(
			self.backend,
			self.changes_trie_storage.clone(),
			self.overlay
		);
		let root_and_tx = root_and_tx.map(|(root, changes)| {
			let mut calculated_root = Default::default();
			let mut mdb = MemoryDB::new();
			{
				let mut trie = TrieDBMut::<H, C>::new(&mut mdb, &mut calculated_root);
				for (key, value) in changes {
					trie.insert(&key, &value).expect(EXT_NOT_ALLOWED_TO_FAIL);
				}
			}

			(mdb, root)
		});
		let root = root_and_tx.as_ref().map(|(_, root)| root.clone());
		self.changes_trie_transaction = Some(root_and_tx);
		root
	}
}

#[cfg(test)]
mod tests {
	use primitives::{KeccakHasher, RlpCodec};
	use backend::InMemory;
	use changes_trie::{Configuration as ChangesTrieConfiguration,
		InMemoryStorage as InMemoryChangesTrieStorage};
	use super::*;

	type TestBackend = InMemory<KeccakHasher, RlpCodec>;
	type TestChangesTrieStorage = InMemoryChangesTrieStorage<KeccakHasher>;
	type TestExt<'a> = Ext<'a, KeccakHasher, RlpCodec, TestBackend, TestChangesTrieStorage>;

	fn prepare_overlay_with_changes() -> OverlayedChanges {
		OverlayedChanges {
			prospective: vec![
				(vec![1], (Some(vec![100].into_iter().collect()), Some(vec![1].into_iter().collect())))
			].into_iter().collect(),
			committed: Default::default(),
			changes_trie_config: Some(ChangesTrieConfiguration {
				digest_interval: 0,
				digest_levels: 0,
			}),
			block: Some(100),
			extrinsic: Some(3),
		}
	}

	#[test]
	fn storage_changes_root_is_none_when_storage_is_not_provided() {
		let mut overlay = prepare_overlay_with_changes();
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, None);
		assert_eq!(ext.storage_changes_root(), None);
	}

	#[test]
	fn storage_changes_root_is_none_when_extrinsic_changes_are_none() {
		let mut overlay = prepare_overlay_with_changes();
		overlay.changes_trie_config = None;
		let storage = TestChangesTrieStorage::new();
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, Some(&storage));
		assert_eq!(ext.storage_changes_root(), None);
	}

	#[test]
	fn storage_changes_root_is_some_when_extrinsic_changes_are_non_empty() {
		let mut overlay = prepare_overlay_with_changes();
		let storage = TestChangesTrieStorage::new();
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, Some(&storage));
		assert_eq!(ext.storage_changes_root(),
			Some(hex!("39c072f9c91d3adda925f84a197d67ab0fef16c12fe0587d72d25da177332bba").into()));
	}

	#[test]
	fn storage_changes_root_is_some_when_extrinsic_changes_are_empty() {
		let mut overlay = prepare_overlay_with_changes();
		overlay.prospective.get_mut(&vec![1]).unwrap().1 = None;
		let storage = TestChangesTrieStorage::new();
		let backend = TestBackend::default();
		let mut ext = TestExt::new(&mut overlay, &backend, Some(&storage));
		assert_eq!(ext.storage_changes_root(),
			Some(hex!("56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421").into()));
	}
}
