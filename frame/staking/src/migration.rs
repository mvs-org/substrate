use super::*;

use frame_support::weights::Weight;

/// Deprecated storages used for migration only.
mod deprecated {
	use crate::{BalanceOf, Exposure, SessionIndex, Trait};
	use codec::{Decode, Encode};
	use frame_support::{decl_module, decl_storage};
	use sp_std::prelude::*;

	// edgeware uses `u64` for `Moment`
	pub type Moment = u64;

	/// Reward points of an era. Used to split era total payout between validators.
	#[derive(Encode, Decode, Default)]
	pub struct EraPoints {
		/// Total number of points. Equals the sum of reward points for each validator.
		pub total: u32,
		/// The reward points earned by a given validator. The index of this vec corresponds to the
		/// index into the current validator set.
		pub individual: Vec<u32>,
	}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin { }
	}

	decl_storage! {
		pub trait Store for Module<T: Trait> as Staking {
			pub SlotStake: BalanceOf<T>;

			/// The currently elected validator set keyed by stash account ID.
			pub CurrentElected: Vec<T::AccountId>;

			/// The start of the current era.
			pub CurrentEraStart: Moment;

			/// The session index at which the current era started.
			pub CurrentEraStartSessionIndex: SessionIndex;

			/// Rewards for the current era. Using indices of current elected set.
			pub CurrentEraPointsEarned: EraPoints;

			/// Nominators for a particular account that is in action right now. You can't iterate
			/// through validators here, but you can find them in the Session module.
			///
			/// This is keyed by the stash account.
			pub Stakers: map hasher(opaque_blake2_256) T::AccountId => Exposure<T::AccountId, BalanceOf<T>>;

			pub StorageVersion: u32;
		}
	}
}

#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
struct OldStakingLedger<AccountId, Balance: HasCompact> {
	pub stash: AccountId,
	#[codec(compact)]
	pub total: Balance,
	#[codec(compact)]
	pub active: Balance,
	pub unlocking: Vec<UnlockChunk<Balance>>,
}

/// Update storages to current version
///
/// In old version the staking module has several issue about handling session delay, the
/// current era was always considered the active one.
///
/// After the migration the current era will still be considered the active one for the era of
/// the upgrade. And the delay issue will be fixed when planning the next era.
// * create:
//   * ActiveEraStart
//   * ErasRewardPoints
//   * ActiveEra
//   * ErasStakers
//   * ErasStakersClipped
//   * ErasValidatorPrefs
//   * ErasTotalStake
//   * ErasStartSessionIndex
// * translate StakingLedger
// * removal of:
//   * Stakers
//   * SlotStake
//   * CurrentElected
//   * CurrentEraStart
//   * CurrentEraStartSessionIndex
//   * CurrentEraPointsEarned
//
// The edgeware migration is so big we just assume it consumes the whole block.
pub fn migrate_to_simple_payouts<T: Trait>() -> Weight {
	let version = deprecated::StorageVersion::take();
	if version != 2 {
		frame_support::runtime_print!("🕊️  Unexpected Staking StorageVersion: {}", version);
		return 0;
	}
	sp_runtime::print("🕊️  Migrating Staking...");
	let current_era_start_index = deprecated::CurrentEraStartSessionIndex::get();
	let current_era = <Module<T> as Store>::CurrentEra::get().unwrap_or(0);
	let current_era_start = deprecated::CurrentEraStart::get();
	<Module<T> as Store>::ErasStartSessionIndex::insert(current_era, current_era_start_index);
	<Module<T> as Store>::ActiveEra::put(ActiveEraInfo {
		index: current_era,
		start: Some(current_era_start),
	});

	let current_elected = deprecated::CurrentElected::<T>::get();
	let mut current_total_stake = <BalanceOf<T>>::zero();
	for validator in &current_elected {
		let exposure = deprecated::Stakers::<T>::get(validator);
		current_total_stake += exposure.total;
		<Module<T> as Store>::ErasStakers::insert(current_era, validator, &exposure);

		let mut exposure_clipped = exposure;
		let clipped_max_len = T::MaxNominatorRewardedPerValidator::get() as usize;
		if exposure_clipped.others.len() > clipped_max_len {
			exposure_clipped
				.others
				.sort_unstable_by(|a, b| a.value.cmp(&b.value).reverse());
			exposure_clipped.others.truncate(clipped_max_len);
		}
		<Module<T> as Store>::ErasStakersClipped::insert(current_era, validator, exposure_clipped);

		let pref = <Module<T> as Store>::Validators::get(validator);
		<Module<T> as Store>::ErasValidatorPrefs::insert(current_era, validator, pref);
	}
	<Module<T> as Store>::ErasTotalStake::insert(current_era, current_total_stake);

	let points = deprecated::CurrentEraPointsEarned::get();
	<Module<T> as Store>::ErasRewardPoints::insert(
		current_era,
		EraRewardPoints {
			total: points.total,
			individual: current_elected
				.iter()
				.cloned()
				.zip(points.individual.iter().cloned())
				.collect(),
		},
	);

	let res = <Module<T> as Store>::Ledger::translate_values(
		|old: OldStakingLedger<T::AccountId, BalanceOf<T>>| StakingLedger {
			stash: old.stash,
			total: old.total,
			active: old.active,
			unlocking: old.unlocking,
			claimed_rewards: vec![],
		},
	);
	if let Err(e) = res {
		frame_support::print("Encountered error in migration of Staking::Ledger map.");
		frame_support::print("The number of removed key/value is:");
		frame_support::print(e);
	}

	// Kill old storages
	deprecated::Stakers::<T>::remove_all();
	deprecated::SlotStake::<T>::kill();
	deprecated::CurrentElected::<T>::kill();
	deprecated::CurrentEraStart::kill();
	deprecated::CurrentEraStartSessionIndex::kill();
	deprecated::CurrentEraPointsEarned::kill();

	StorageVersion::put(Releases::V4_0_0);

	sp_runtime::print("🕊️  Done Staking.");
	T::MaximumBlockWeight::get()
}

#[cfg(test)]
mod tests {
	use super::*;
	use mock::*;

	use codec::Encode;
	use frame_support::migration::put_storage_value;
	use sp_core::blake2_256;

	use substrate_test_utils::assert_eq_uvec;
	use sp_runtime::assert_eq_error_rate;

	#[test]
	fn lazy_payouts_upgrade_works() {
		ExtBuilder::default().build().execute_with(|| {
			start_era(3);

			assert_eq!(Session::validators(), vec![21, 11]);

			// Insert fake data to check the migration
			put_storage_value::<Vec<AccountId>>(b"Staking", b"CurrentElected", b"", vec![21, 31]);
			put_storage_value::<SessionIndex>(b"Staking", b"CurrentEraStartSessionIndex", b"", 5);
			put_storage_value::<deprecated::Moment>(b"Staking", b"CurrentEraStart", b"", 777);
			put_storage_value(
				b"Staking",
				b"Stakers",
				&blake2_256(&11u64.encode()),
				Exposure::<AccountId, Balance> {
					total: 10,
					own: 10,
					others: vec![],
				},
			);
			put_storage_value(
				b"Staking",
				b"Stakers",
				&blake2_256(&21u64.encode()),
				Exposure::<AccountId, Balance> {
					total: 20,
					own: 20,
					others: vec![],
				},
			);
			put_storage_value(
				b"Staking",
				b"Stakers",
				&blake2_256(&31u64.encode()),
				Exposure::<AccountId, Balance> {
					total: 30,
					own: 30,
					others: vec![],
				},
			);
			put_storage_value::<(u32, Vec<u32>)>(
				b"Staking",
				b"CurrentEraPointsEarned",
				b"",
				(12, vec![2, 10]),
			);
			<Staking as Store>::ErasStakers::remove_all();
			<Staking as Store>::ErasStakersClipped::remove_all();
			deprecated::StorageVersion::put(2);

			// Perform upgrade
			migrate_to_simple_payouts::<Test>();

			assert_eq!(<Staking as Store>::StorageVersion::get(), Releases::V4_0_0);

			// Check migration
			assert_eq!(<Staking as Store>::ErasStartSessionIndex::get(3).unwrap(), 5);
			assert_eq!(
				<Staking as Store>::ErasRewardPoints::get(3),
				EraRewardPoints {
					total: 12,
					individual: vec![(21, 2), (31, 10)].into_iter().collect(),
				}
			);
			assert_eq!(<Staking as Store>::ActiveEra::get().unwrap().index, 3);
			assert_eq!(<Staking as Store>::ActiveEra::get().unwrap().start, Some(777));
			assert_eq!(<Staking as Store>::CurrentEra::get().unwrap(), 3);
			assert_eq!(
				<Staking as Store>::ErasStakers::get(3, 11),
				Exposure {
					total: 0,
					own: 0,
					others: vec![],
				}
			);
			assert_eq!(
				<Staking as Store>::ErasStakers::get(3, 21),
				Exposure {
					total: 20,
					own: 20,
					others: vec![],
				}
			);
			assert_eq!(
				<Staking as Store>::ErasStakers::get(3, 31),
				Exposure {
					total: 30,
					own: 30,
					others: vec![],
				}
			);
			assert_eq!(
				<Staking as Store>::ErasStakersClipped::get(3, 11),
				Exposure {
					total: 0,
					own: 0,
					others: vec![],
				}
			);
			assert_eq!(
				<Staking as Store>::ErasStakersClipped::get(3, 21),
				Exposure {
					total: 20,
					own: 20,
					others: vec![],
				}
			);
			assert_eq!(
				<Staking as Store>::ErasStakersClipped::get(3, 31),
				Exposure {
					total: 30,
					own: 30,
					others: vec![],
				}
			);
			assert_eq!(
				<Staking as Store>::ErasValidatorPrefs::get(3, 21),
				Staking::validators(21)
			);
			assert_eq!(
				<Staking as Store>::ErasValidatorPrefs::get(3, 31),
				Staking::validators(31)
			);
			assert_eq!(<Staking as Store>::ErasTotalStake::get(3), 50);
		})
	}

	#[test]
	fn test_last_reward_migration() {
		use sp_storage::Storage;

		let mut s = Storage::default();

		let old_staking10 = OldStakingLedger::<u64, u64> {
			stash: 0,
			total: 10,
			active: 10,
			unlocking: vec![UnlockChunk { value: 1234, era: 56 }],
		};

		let old_staking11 = OldStakingLedger::<u64, u64> {
			stash: 1,
			total: 0,
			active: 0,
			unlocking: vec![],
		};

		let old_staking12 = OldStakingLedger::<u64, u64> {
			stash: 2,
			total: 100,
			active: 100,
			unlocking: vec![
				UnlockChunk { value: 9876, era: 54 },
				UnlockChunk { value: 98, era: 76 },
			],
		};

		let old_staking13 = OldStakingLedger::<u64, u64> {
			stash: 3,
			total: 100,
			active: 100,
			unlocking: vec![],
		};

		let data = vec![
			(
				Ledger::<Test>::hashed_key_for(10),
				old_staking10.encode().to_vec(),
			),
			(
				Ledger::<Test>::hashed_key_for(11),
				old_staking11.encode().to_vec(),
			),
			(
				Ledger::<Test>::hashed_key_for(12),
				old_staking12.encode().to_vec(),
			),
			(
				Ledger::<Test>::hashed_key_for(13),
				old_staking13.encode().to_vec(),
			),
		];

		s.top = data.into_iter().collect();
		sp_io::TestExternalities::new(s).execute_with(|| {
			HistoryDepth::put(84);
			CurrentEra::put(99);
			let nominations = Nominations::<u64> {
				targets: vec![],
				submitted_in: 0,
				suppressed: false,
			};
			Nominators::<Test>::insert(3, nominations);
			Bonded::<Test>::insert(3, 13);
			deprecated::StorageVersion::put(2);
			// migrate
			migrate_to_simple_payouts::<Test>();
			// Test staker out of range
			assert_eq!(
				Ledger::<Test>::get(10),
				Some(StakingLedger {
					stash: 0,
					total: 10,
					active: 10,
					unlocking: vec![UnlockChunk { value: 1234, era: 56 }],
					claimed_rewards: vec![],
				})
			);
			// Test staker none
			assert_eq!(
				Ledger::<Test>::get(11),
				Some(StakingLedger {
					stash: 1,
					total: 0,
					active: 0,
					unlocking: vec![],
					claimed_rewards: vec![],
				})
			);
			// Test staker migration
			assert_eq!(
				Ledger::<Test>::get(12),
				Some(StakingLedger {
					stash: 2,
					total: 100,
					active: 100,
					unlocking: vec![
						UnlockChunk { value: 9876, era: 54 },
						UnlockChunk { value: 98, era: 76 }
					],
					claimed_rewards: vec![],
				})
			);
			// Test nominator migration
			assert_eq!(
				Ledger::<Test>::get(13),
				Some(StakingLedger {
					stash: 3,
					total: 100,
					active: 100,
					unlocking: vec![],
					claimed_rewards: vec![],
				})
			);
		});
	}

	#[test]
	fn rewards_should_work_before_migration() {
		// should check that before migration:
		// * rewards get recorded per session
		// * rewards get paid per Era
		// * Check that nominators are also rewarded
		ExtBuilder::default().nominate(true).build().execute_with(|| {
			let init_balance_10 = Balances::total_balance(&10);
			let init_balance_11 = Balances::total_balance(&11);
			let init_balance_20 = Balances::total_balance(&20);
			let init_balance_21 = Balances::total_balance(&21);
			let init_balance_100 = Balances::total_balance(&100);
			let init_balance_101 = Balances::total_balance(&101);

			// Check state
			Payee::<Test>::insert(11, RewardDestination::Controller);
			Payee::<Test>::insert(21, RewardDestination::Controller);
			Payee::<Test>::insert(101, RewardDestination::Controller);

			<Module<Test>>::reward_by_ids(vec![(11, 50)]);
			<Module<Test>>::reward_by_ids(vec![(11, 50)]);
			// This is the second validator of the current elected set.
			<Module<Test>>::reward_by_ids(vec![(21, 50)]);

			// Compute total payout now for whole duration as other parameter won't change
			let total_payout_0 = current_total_payout_for_duration(3 * 1000);
			assert!(total_payout_0 > 10); // Test is meaningful if reward something

			start_session(1);

			assert_eq!(Balances::total_balance(&10), init_balance_10);
			assert_eq!(Balances::total_balance(&11), init_balance_11);
			assert_eq!(Balances::total_balance(&20), init_balance_20);
			assert_eq!(Balances::total_balance(&21), init_balance_21);
			assert_eq!(Balances::total_balance(&100), init_balance_100);
			assert_eq!(Balances::total_balance(&101), init_balance_101);
			assert_eq_uvec!(Session::validators(), vec![11, 21]);
			assert_eq!(
				Staking::eras_reward_points(Staking::active_era().unwrap().index),
				EraRewardPoints {
					total: 50 * 3,
					individual: vec![(11, 100), (21, 50)].into_iter().collect(),
				}
			);
			let part_for_10 = Perbill::from_rational_approximation::<u32>(1000, 1125);
			let part_for_20 = Perbill::from_rational_approximation::<u32>(1000, 1375);
			let part_for_100_from_10 = Perbill::from_rational_approximation::<u32>(125, 1125);
			let part_for_100_from_20 = Perbill::from_rational_approximation::<u32>(375, 1375);

			start_session(2);
			start_session(3);

			assert_eq!(Staking::active_era().unwrap().index, 1);
			mock::make_all_reward_payment_before_migration(0);

			assert_eq_error_rate!(
				Balances::total_balance(&10),
				init_balance_10 + part_for_10 * total_payout_0 * 2 / 3,
				2
			);
			assert_eq_error_rate!(Balances::total_balance(&11), init_balance_11, 2);
			assert_eq_error_rate!(
				Balances::total_balance(&20),
				init_balance_20 + part_for_20 * total_payout_0 * 1 / 3,
				2
			);
			assert_eq_error_rate!(Balances::total_balance(&21), init_balance_21, 2);
			assert_eq_error_rate!(
				Balances::total_balance(&100),
				init_balance_100
					+ part_for_100_from_10 * total_payout_0 * 2 / 3
					+ part_for_100_from_20 * total_payout_0 * 1 / 3,
				2
			);
			assert_eq_error_rate!(Balances::total_balance(&101), init_balance_101, 2);

			assert_eq_uvec!(Session::validators(), vec![11, 21]);
			<Module<Test>>::reward_by_ids(vec![(11, 1)]);

			// Compute total payout now for whole duration as other parameter won't change
			let total_payout_1 = current_total_payout_for_duration(3 * 1000);
			assert!(total_payout_1 > 10); // Test is meaningful if reward something

			mock::start_era(2);
			mock::make_all_reward_payment_before_migration(1);

			assert_eq_error_rate!(
				Balances::total_balance(&10),
				init_balance_10 + part_for_10 * (total_payout_0 * 2 / 3 + total_payout_1),
				2
			);
			assert_eq_error_rate!(Balances::total_balance(&11), init_balance_11, 2);
			assert_eq_error_rate!(
				Balances::total_balance(&20),
				init_balance_20 + part_for_20 * total_payout_0 * 1 / 3,
				2
			);
			assert_eq_error_rate!(Balances::total_balance(&21), init_balance_21, 2);
			assert_eq_error_rate!(
				Balances::total_balance(&100),
				init_balance_100
					+ part_for_100_from_10 * (total_payout_0 * 2 / 3 + total_payout_1)
					+ part_for_100_from_20 * total_payout_0 * 1 / 3,
				2
			);
			assert_eq_error_rate!(Balances::total_balance(&101), init_balance_101, 2);
		});
	}

	#[test]
	fn migrate_era_should_work() {
		// should check that before and after migration:
		// * rewards get recorded per session
		// * rewards get paid per Era
		// * Check that nominators are also rewarded
		ExtBuilder::default().nominate(true).build().execute_with(|| {
			let init_balance_10 = Balances::total_balance(&10);
			let init_balance_11 = Balances::total_balance(&11);
			let init_balance_20 = Balances::total_balance(&20);
			let init_balance_21 = Balances::total_balance(&21);
			let init_balance_100 = Balances::total_balance(&100);
			let init_balance_101 = Balances::total_balance(&101);

			// Check state
			Payee::<Test>::insert(11, RewardDestination::Controller);
			Payee::<Test>::insert(21, RewardDestination::Controller);
			Payee::<Test>::insert(101, RewardDestination::Controller);

			<Module<Test>>::reward_by_ids(vec![(11, 50)]);
			<Module<Test>>::reward_by_ids(vec![(11, 50)]);
			// This is the second validator of the current elected set.
			<Module<Test>>::reward_by_ids(vec![(21, 50)]);

			// Compute total payout now for whole duration as other parameter won't change
			let total_payout_0 = current_total_payout_for_duration(3 * 1000);
			assert!(total_payout_0 > 10); // Test is meaningful if reward something

			start_session(1);

			assert_eq!(Balances::total_balance(&10), init_balance_10);
			assert_eq!(Balances::total_balance(&11), init_balance_11);
			assert_eq!(Balances::total_balance(&20), init_balance_20);
			assert_eq!(Balances::total_balance(&21), init_balance_21);
			assert_eq!(Balances::total_balance(&100), init_balance_100);
			assert_eq!(Balances::total_balance(&101), init_balance_101);
			assert_eq_uvec!(Session::validators(), vec![11, 21]);
			assert_eq!(
				Staking::eras_reward_points(Staking::active_era().unwrap().index),
				EraRewardPoints {
					total: 50 * 3,
					individual: vec![(11, 100), (21, 50)].into_iter().collect(),
				}
			);
			let part_for_10 = Perbill::from_rational_approximation::<u32>(1000, 1125);
			let part_for_20 = Perbill::from_rational_approximation::<u32>(1000, 1375);
			let part_for_100_from_10 = Perbill::from_rational_approximation::<u32>(125, 1125);
			let part_for_100_from_20 = Perbill::from_rational_approximation::<u32>(375, 1375);

			start_session(2);
			start_session(3);

			assert_eq!(Staking::active_era().unwrap().index, 1);
			mock::make_all_reward_payment_before_migration(0);

			assert_eq_error_rate!(
				Balances::total_balance(&10),
				init_balance_10 + part_for_10 * total_payout_0 * 2 / 3,
				2
			);
			assert_eq_error_rate!(Balances::total_balance(&11), init_balance_11, 2);
			assert_eq_error_rate!(
				Balances::total_balance(&20),
				init_balance_20 + part_for_20 * total_payout_0 * 1 / 3,
				2
			);
			assert_eq_error_rate!(Balances::total_balance(&21), init_balance_21, 2);
			assert_eq_error_rate!(
				Balances::total_balance(&100),
				init_balance_100
					+ part_for_100_from_10 * total_payout_0 * 2 / 3
					+ part_for_100_from_20 * total_payout_0 * 1 / 3,
				2
			);
			assert_eq_error_rate!(Balances::total_balance(&101), init_balance_101, 2);

			assert_eq_uvec!(Session::validators(), vec![11, 21]);
			<Module<Test>>::reward_by_ids(vec![(11, 1)]);

			// Compute total payout now for whole duration as other parameter won't change
			let total_payout_1 = current_total_payout_for_duration(3 * 1000);
			assert!(total_payout_1 > 10); // Test is meaningful if reward something

			mock::start_era(2);
			mock::make_all_reward_payment(1);

			assert_eq_error_rate!(
				Balances::total_balance(&10),
				init_balance_10 + part_for_10 * (total_payout_0 * 2 / 3 + total_payout_1),
				2
			);
			assert_eq_error_rate!(Balances::total_balance(&11), init_balance_11, 2);
			assert_eq_error_rate!(
				Balances::total_balance(&20),
				init_balance_20 + part_for_20 * total_payout_0 * 1 / 3,
				2
			);
			assert_eq_error_rate!(Balances::total_balance(&21), init_balance_21, 2);
			assert_eq_error_rate!(
				Balances::total_balance(&100),
				init_balance_100
					+ part_for_100_from_10 * (total_payout_0 * 2 / 3 + total_payout_1)
					+ part_for_100_from_20 * total_payout_0 * 1 / 3,
				2
			);
			assert_eq_error_rate!(Balances::total_balance(&101), init_balance_101, 2);
		});
	}
}
