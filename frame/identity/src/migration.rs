use super::*;

use frame_support::storage::migration::{
	put_storage_value,
};
use frame_support::{
	Twox128,
	Twox64Concat,
	Blake2_128Concat,
	StorageHasher
};
// use sp_io::hashing::{
// 	// blake2_128, blake2_256, twox_64, twox_256
// 	twox_128,
// };
use frame_support::weights::Weight;
// use sp_io::hashing::twox_64;

pub fn on_runtime_upgrade<T: Trait>() -> Weight{
	let _module_prefix_hashed: [u8; 16] = Twox128::hash(b"Identity");
	sp_runtime::print("🕊️  Migrating Identities...");
	if let Ok(identities) = Vec::<([u8; 32], Registration<BalanceOf<T>>)>::decode(&mut &include_bytes!("identities.scale")[..]) {
		let _storage_prefix_hashed: [u8; 16] = Twox128::hash(b"IdentityOf");
		for iden in &identities {
			sp_runtime::print("🕊️  Migrating identity records");
			let _twoxx_hash_concat: Vec<u8> = Twox64Concat::hash(&iden.0);
			let mut hash = _module_prefix_hashed.to_vec();
			hash.extend(&_storage_prefix_hashed);
			hash.extend(&_twoxx_hash_concat);
			put_storage_value(b"Identity", b"IdentityOf", &hash, iden.1.clone());
		}
	}

	if let Ok(subids) = Vec::<([u8; 32], (BalanceOf<T>, Vec<T::AccountId>))>::decode(&mut &include_bytes!("subidentities.scale")[..]) {
		let _storage_prefix_hashed: [u8; 16] = Twox128::hash(b"SubsOf");
		for subid in &subids {
			sp_runtime::print("🕊️  Migrating subidentity records");
			let _twoxx_hash_concat: Vec<u8> = Blake2_128Concat::hash(&subid.0);
			let mut hash = _module_prefix_hashed.to_vec();
			hash.extend(&_storage_prefix_hashed);
			hash.extend(&_twoxx_hash_concat);
			put_storage_value(b"Identity", b"SubsOf", &hash, subid.1.clone());
		}
	}

	if let Ok(superids) = Vec::<([u8; 32], (T::AccountId, Data))>::decode(&mut &include_bytes!("superidentities.scale")[..]) {
		let _storage_prefix_hashed: [u8; 16] = Twox128::hash(b"SuperOf");
		for superid in &superids {
			sp_runtime::print("🕊️  Migrating superidentity records");
			let _twoxx_hash_concat: Vec<u8> = Twox64Concat::hash(&superid.0);
			let mut hash = _module_prefix_hashed.to_vec();
			hash.extend(&_storage_prefix_hashed);
			hash.extend(&_twoxx_hash_concat);
			put_storage_value(b"Identity", b"SuperOf", &hash, superid.1.clone());
		}
	}

	sp_runtime::print("🕊️  Done Identities.");
	T::MaximumBlockWeight::get()
} 