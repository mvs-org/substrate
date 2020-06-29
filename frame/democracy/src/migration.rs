
use super::*;

mod deprecated {
	use sp_std::prelude::*;

	use codec::{Encode, EncodeLike, Decode, Input, Output};
	use frame_support::{decl_module, decl_storage};
	use sp_runtime::RuntimeDebug;
	use sp_std::convert::TryFrom;

	use crate::{Trait, ReferendumIndex, Conviction};

	#[derive(Copy, Clone, Eq, PartialEq, Default, RuntimeDebug)]
	pub struct Vote {
		pub aye: bool,
		pub conviction: Conviction,
	}

	impl Encode for Vote {
		fn encode_to<T: Output>(&self, output: &mut T) {
			output.push_byte(u8::from(self.conviction) | if self.aye { 0b1000_0000 } else { 0 });
		}
	}

	impl EncodeLike for Vote {}

	impl Decode for Vote {
		fn decode<I: Input>(input: &mut I) -> core::result::Result<Self, codec::Error> {
			let b = input.read_byte()?;
			Ok(Vote {
				aye: (b & 0b1000_0000) == 0b1000_0000,
				conviction: Conviction::try_from(b & 0b0111_1111)
					.map_err(|_| codec::Error::from("Invalid conviction"))?,
			})
		}
	}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin { }
	}
	decl_storage! {
		trait Store for Module<T: Trait> as Democracy {
			pub VotersFor get(fn voters_for):
				map hasher(opaque_blake2_256) ReferendumIndex => Vec<T::AccountId>;
			pub VoteOf get(fn vote_of):
				map hasher(opaque_blake2_256) (ReferendumIndex, T::AccountId) => Vote;
			pub Proxy get(fn proxy):
				map hasher(opaque_blake2_256) T::AccountId => Option<T::AccountId>;
			pub Delegations get(fn delegations):
				map hasher(opaque_blake2_256) T::AccountId => (T::AccountId, Conviction);
		}
	}
}

pub fn migrate_account<T: Trait>() {
	Locks::<T>::migrate_key_from_blake(a);
}

pub fn migrate_all<T: Trait>() -> Weight {
	sp_runtime::print("🕊️  Migrating Democracy...");
	let mut weight = 0;
	weight += migrate_hasher();
	weight += migrate_remove_unused_storage();
	weight += migrate_referendum_info();
	sp_runtime::print("🕊️  Done Democracy.");
	weight
}

pub fn migrate_hasher<T: Trait>() -> Weight {
	// TODO: is this valid?
	Blacklist::<T>::remove_all();
	Cancellations::<T>::remove_all();
	// ReferendumInfoOf is migrated in `migrate_referendum_info`
	for (p, h, _) in PublicProps::<T>::get().into_iter() {
		DepositOf::<T>::migrate_key_from_blake(p);
		Preimages::<T>::migrate_key_from_blake(h);
	}
	// TODO: figure out actual weight
	0
}

pub fn migrate_remove_unused_storage() -> Weight {
	// TODO: is this valid?
	deprecated::VotersFor::<T>::remove_all();
	deprecated::VoteOf::<T>::remove_all();
	deprecated::Proxy::<T>::remove_all();
	deprecated::Delegations::<T>::remove_all();
	// TODO: figure out actual weight
	0
}

// migration based on [substrate/#5294](https://github.com/paritytech/substrate/pull/5294)
pub fn migrate_referendum_info() -> Weight {
	use frame_support::{Twox64Concat, migration::{StorageKeyIterator, remove_storage_prefix}};
	
	let range = LowestUnbaked::get()..ReferendumCount::get();
	for (index, (end, proposal_hash, threshold, delay))
		in StorageKeyIterator::<
			ReferendumIndex,
			(T::BlockNumber, T::Hash, VoteThreshold, T::BlockNumber),
			Blake2_256,
		>::new(b"Democracy", b"ReferendumInfoOf").drain()
	{
		if range.contains(index) {
			let status = ReferendumStatus {
				end, proposal_hash, threshold, delay, tally: Tally::default()
			};
			ReferendumInfoOf::<T>::insert(index, ReferendumInfo::Ongoing(status))
		}
	}
	// TODO: figure out actual weight
	0
}