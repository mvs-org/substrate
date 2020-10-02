use super::*;

use frame_support::storage::migration::{
	put_storage_value,
};
use frame_support::{
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

pub fn on_runtime_upgrade<T: Trait>() -> Weight {
	sp_runtime::print("🕊️  Migrating Identities...");
	if let Ok(identities) = Vec::<([u8; 32], Registration<BalanceOf<T>>)>::decode(&mut &include_bytes!("identities.scale")[..]) {
		for iden in &identities {
			sp_runtime::print("🕊️  Migrating identity records");
			put_storage_value(b"Identity", b"IdentityOf", &Twox64Concat::hash(&iden.0), iden.1.clone());
		}
	}

	if let Ok(subids) = Vec::<([u8; 32], (BalanceOf<T>, Vec<T::AccountId>))>::decode(&mut &include_bytes!("subidentities.scale")[..]) {
		for subid in &subids {
			sp_runtime::print("🕊️  Migrating subidentity records");
			put_storage_value(b"Identity", b"SubsOf", &Twox64Concat::hash(&subid.0), subid.1.clone());
		}
	}

	if let Ok(superids) = Vec::<([u8; 32], (T::AccountId, Data))>::decode(&mut &include_bytes!("superidentities.scale")[..]) {
		for superid in &superids {
			sp_runtime::print("🕊️  Migrating superidentity records");
			put_storage_value(b"Identity", b"SuperOf", &Blake2_128Concat::hash(&superid.0), superid.1.clone());
		}
	}

	sp_runtime::print("🕊️  Done Identities.");
	T::MaximumBlockWeight::get()
} 