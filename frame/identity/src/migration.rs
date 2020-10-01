use super::*;

use frame_support::storage::migration::{
	put_storage_value, StorageIterator,
};
use frame_support::weights::Weight;
// use sp_io::hashing::twox_64;

pub fn on_runtime_upgrade<T: Trait>() -> Weight{
	sp_runtime::print("🕊️  Migrating Identities...");
	for (hash, registration) in StorageIterator::<Registration<BalanceOf<T>>>::new(b"Identity", b"IdentityOf").drain() {
		sp_runtime::print("🕊️  Migrating identity records");
		put_storage_value(b"Identity", b"IdentityOf", &hash, registration);
	}

	for (hash, subid) in StorageIterator::<(BalanceOf<T>, Vec<T::AccountId>)>::new(b"Identity", b"SubsOf").drain() {
		sp_runtime::print("🕊️  Migrating subidentity records");
		put_storage_value(b"Identity", b"SubsOf", &hash, subid);
	}

	for (hash, superid) in StorageIterator::<(T::AccountId, Data)>::new(b"Identity", b"SuperOf").drain() {
		sp_runtime::print("🕊️  Migrating superidentity records");
		put_storage_value(b"Identity", b"SuperOf", &hash, superid);
	}

	sp_runtime::print("🕊️  Done Identities.");
	T::MaximumBlockWeight::get()
}