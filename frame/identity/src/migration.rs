use super::*;
use frame_support::storage::migration::{put_storage_value};

pub fn on_runtime_upgrade<T: Trait>() -> Weight{
	sp_runtime::print("🕊️  Migrating Identities...");
	if let Ok(identities) = Vec::<(sp_core::H256, Registration<BalanceOf<T>>)>::decode(&mut &include_bytes!("identities.scale")[..]) {
		for iden in &identities {
			sp_runtime::print("🕊️  Migrating identity records");
			put_storage_value(b"Identity", b"IdentityOf", &<[u8; 32]>::from(iden.0), iden.1.clone());
		}
	}

	if let Ok(subids) = Vec::<(sp_core::H256, (BalanceOf<T>, Vec<T::AccountId>))>::decode(&mut &include_bytes!("subidentities.scale")[..]) {
		for subid in &subids {
			sp_runtime::print("🕊️  Migrating subidentity records");
			put_storage_value(b"Identity", b"SubsOf", &<[u8; 32]>::from(subid.0), subid.1.clone());
		}
	}

	if let Ok(superids) = Vec::<(sp_core::H256, (T::AccountId, Data))>::decode(&mut &include_bytes!("superidentities.scale")[..]) {
		for superid in &superids {
			sp_runtime::print("🕊️  Migrating superidentity records");
			put_storage_value(b"Identity", b"SuperOf", &<[u8; 32]>::from(superid.0), superid.1.clone());
		}
	}

	sp_runtime::print("🕊️  Done Identities.");
	T::MaximumBlockWeight::get()
}