// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! A `CodeExecutor` specialisation which uses natively compiled runtime when the wasm to be
//! executed is equivalent to the natively compiled code.

extern crate demo_runtime;
#[macro_use] extern crate substrate_executor;
extern crate substrate_codec as codec;
extern crate substrate_state_machine as state_machine;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_primitives as primitives;
extern crate demo_primitives;
extern crate ed25519;
extern crate triehash;

#[cfg(test)] extern crate substrate_keyring as keyring;
#[cfg(test)] extern crate substrate_runtime_primitives as runtime_primitives;
#[cfg(test)] extern crate substrate_runtime_support as runtime_support;
#[cfg(test)] extern crate substrate_runtime_balances as balances;
#[cfg(test)] extern crate substrate_runtime_session as session;
#[cfg(test)] extern crate substrate_runtime_staking as staking;
#[cfg(test)] extern crate substrate_runtime_system as system;
#[cfg(test)] extern crate substrate_runtime_consensus as consensus;
#[cfg(test)] #[macro_use] extern crate hex_literal;

pub use substrate_executor::NativeExecutor;
native_executor_instance!(pub Executor, demo_runtime::api::dispatch, demo_runtime::VERSION, include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm"));

#[cfg(test)]
mod tests {
	use runtime_io;
	use super::Executor;
	use substrate_executor::{WasmExecutor, NativeExecutionDispatch};
	use codec::{Encode, Decode, Joiner};
	use keyring::Keyring;
	use runtime_support::{Hashable, StorageValue, StorageMap};
	use state_machine::{CodeExecutor, Externalities, TestExternalities};
	use primitives::{twox_128, KeccakHasher, RlpCodec, ChangesTrieConfiguration};
	use demo_primitives::{Hash, BlockNumber, AccountId};
	use runtime_primitives::traits::Header as HeaderT;
	use runtime_primitives::{ApplyOutcome, ApplyError, ApplyResult, MaybeUnsigned};
	use {balances, staking, session, system, consensus};
	use system::{EventRecord, Phase};
	use demo_runtime::{Header, Block, UncheckedExtrinsic, Extrinsic, Call, Concrete, Balances,
		BuildStorage, GenesisConfig, BalancesConfig, SessionConfig, StakingConfig, BareExtrinsic, System,
		SystemConfig, Event};

	use ed25519::{Public, Pair};

	const BLOATY_CODE: &[u8] = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.wasm");
	const COMPACT_CODE: &[u8] = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm");

	// TODO: move into own crate.
	macro_rules! map {
		($( $name:expr => $value:expr ),*) => (
			vec![ $( ( $name, $value ) ),* ].into_iter().collect()
		)
	}

	fn alice() -> AccountId {
		AccountId::from(Keyring::Alice.to_raw_public())
	}

	fn bob() -> AccountId {
		AccountId::from(Keyring::Bob.to_raw_public())
	}

	fn xt() -> UncheckedExtrinsic {
		let extrinsic = BareExtrinsic {
			signed: alice(),
			index: 0,
			function: Call::Balances(balances::Call::transfer::<Concrete>(bob().into(), 69)),
		};
		let signature = MaybeUnsigned(Keyring::from_raw_public(extrinsic.signed.0.clone()).unwrap()
			.sign(&extrinsic.encode()).into());
		let extrinsic = Extrinsic {
			signed: extrinsic.signed.into(),
			index: extrinsic.index,
			function: extrinsic.function,
		};
		UncheckedExtrinsic::new(extrinsic, signature)
	}

	fn from_block_number(n: u64) -> Header {
		Header::new(n, Default::default(), Default::default(), Default::default(), [69; 32].into(), Default::default())
	}

	fn executor() -> ::substrate_executor::NativeExecutor<Executor> {
		::substrate_executor::NativeExecutor::new()
	}

	#[test]
	fn panic_execution_with_foreign_code_gives_error() {
		let mut t = TestExternalities::<KeccakHasher, RlpCodec>::new(map![
			twox_128(&<balances::FreeBalance<Concrete>>::key_for(alice())).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TotalIssuance<Concrete>>::key()).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![70u8; 8],
			twox_128(<balances::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::ExistentialDeposit<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::TransferFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::NextEnumSet<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		]);

		let r = executor().call(&mut t, 8, BLOATY_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let v = executor().call(&mut t, 8, BLOATY_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0.unwrap();
		let r = ApplyResult::decode(&mut &v[..]).unwrap();
		assert_eq!(r, Err(ApplyError::CantPay));
	}

	#[test]
	fn bad_extrinsic_with_native_equivalent_code_gives_error() {
		let mut t = TestExternalities::<KeccakHasher, RlpCodec>::new(map![
			twox_128(&<balances::FreeBalance<Concrete>>::key_for(alice())).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TotalIssuance<Concrete>>::key()).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![70u8; 8],
			twox_128(<balances::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::ExistentialDeposit<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::TransferFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::NextEnumSet<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		]);

		let r = executor().call(&mut t, 8, COMPACT_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let v = executor().call(&mut t, 8, COMPACT_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0.unwrap();
		let r = ApplyResult::decode(&mut &v[..]).unwrap();
		assert_eq!(r, Err(ApplyError::CantPay));
	}

	#[test]
	fn successful_execution_with_native_equivalent_code_gives_ok() {
		let mut t = TestExternalities::<KeccakHasher, RlpCodec>::new(map![
			twox_128(&<balances::FreeBalance<Concrete>>::key_for(alice())).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TotalIssuance<Concrete>>::key()).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::ExistentialDeposit<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::TransferFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::NextEnumSet<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		]);

		let r = executor().call(&mut t, 8, COMPACT_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let r = executor().call(&mut t, 8, COMPACT_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0;
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 42);
			assert_eq!(Balances::total_balance(&bob()), 69);
		});
	}

	#[test]
	fn successful_execution_with_foreign_code_gives_ok() {
		let mut t = TestExternalities::<KeccakHasher, RlpCodec>::new(map![
			twox_128(&<balances::FreeBalance<Concrete>>::key_for(alice())).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TotalIssuance<Concrete>>::key()).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::ExistentialDeposit<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::TransferFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::NextEnumSet<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		]);

		let r = executor().call(&mut t, 8, BLOATY_CODE, "initialise_block", &vec![].and(&from_block_number(1u64)), true).0;
		assert!(r.is_ok());
		let r = executor().call(&mut t, 8, BLOATY_CODE, "apply_extrinsic", &vec![].and(&xt()), true).0;
		assert!(r.is_ok());

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 42);
			assert_eq!(Balances::total_balance(&bob()), 69);
		});
	}

	fn new_test_ext(support_changes_trie: bool) -> TestExternalities<KeccakHasher, RlpCodec> {
		use keyring::Keyring::*;
		let three = [3u8; 32].into();
		TestExternalities::new(GenesisConfig {
			consensus: Some(Default::default()),
			system: Some(SystemConfig {
				changes_trie_config: if support_changes_trie { Some(ChangesTrieConfiguration {
					digest_interval: 2,
					digest_levels: 2,
				}) } else { None },
				..Default::default()
			}),
			balances: Some(BalancesConfig {
				balances: vec![(alice(), 111)],
				transaction_base_fee: 1,
				transaction_byte_fee: 0,
				existential_deposit: 0,
				transfer_fee: 0,
				creation_fee: 0,
				reclaim_rebate: 0,
			}),
			session: Some(SessionConfig {
				session_length: 2,
				validators: vec![One.to_raw_public().into(), Two.to_raw_public().into(), three],
			}),
			staking: Some(StakingConfig {
				sessions_per_era: 2,
				current_era: 0,
				intentions: vec![alice(), bob(), Charlie.to_raw_public().into()],
				validator_count: 3,
				minimum_validator_count: 0,
				bonding_duration: 0,
				early_era_slash: 0,
				session_reward: 0,
				offline_slash_grace: 0,
			}),
			democracy: Some(Default::default()),
			council: Some(Default::default()),
			timestamp: Some(Default::default()),
		}.build_storage().unwrap())
	}

	fn construct_block(number: BlockNumber, parent_hash: Hash, state_root: Hash, changes_root: Option<Hash>, extrinsics: Vec<BareExtrinsic>) -> (Vec<u8>, Hash) {
		use triehash::ordered_trie_root;

		let extrinsics = extrinsics.into_iter().map(|extrinsic| {
			let signature = MaybeUnsigned(Pair::from(Keyring::from_public(Public::from_raw(extrinsic.signed.0.clone())).unwrap())
				.sign(&extrinsic.encode()).into());
			let extrinsic = Extrinsic {
				signed: extrinsic.signed.into(),
				index: extrinsic.index,
				function: extrinsic.function,
			};
			UncheckedExtrinsic::new(extrinsic, signature)
		}).collect::<Vec<_>>();

		let extrinsics_root = ordered_trie_root(extrinsics.iter().map(Encode::encode)).0.into();

		let header = Header {
			parent_hash,
			number,
			state_root,
			changes_root,
			extrinsics_root,
			digest: Default::default(),
		};
		let hash = header.blake2_256();

		(Block { header, extrinsics }.encode(), hash.into())
	}

	fn block1(support_changes_trie: bool) -> (Vec<u8>, Hash) {
		construct_block(
			1,
			[69u8; 32].into(),
			if support_changes_trie {
				hex!("cde8427275a60122e02e06953823f3476566fdf4cdca6eb7ca9df30d35945202").into()
			} else {
				hex!("508a68a0918f614b86b2ccfd0975754f6d2abe1026a34e42d6d8d5abdf4db010").into()
			},
			if support_changes_trie {
				Some(hex!("c8c5b04a9cc5d51a556fd821ca59f34bab64953da1c472860ff686e1270f01b1").into())
			} else {
				None
			},
			vec![BareExtrinsic {
				signed: alice(),
				index: 0,
				function: Call::Balances(balances::Call::transfer(bob().into(), 69)),
			}]
		)
	}

	fn block2() -> (Vec<u8>, Hash) {
		construct_block(
			2,
			block1(false).1,
			hex!("ff6c7facb1e0c2e98c2c49d2ffafa6f56b3b825755bb04a6f14904e6c075eb70").into(),
			None,
			vec![
				BareExtrinsic {
					signed: bob(),
					index: 0,
					function: Call::Balances(balances::Call::transfer(alice().into(), 5)),
				},
				BareExtrinsic {
					signed: alice(),
					index: 1,
					function: Call::Balances(balances::Call::transfer(bob().into(), 15)),
				}
			]
		)
	}

	fn block1big() -> (Vec<u8>, Hash) {
		construct_block(
			1,
			[69u8; 32].into(),
			hex!("e45221804da3a3609454d4e09debe6364cc6af63c2ff067d802d1af62fea32ae").into(),
			None,
			vec![BareExtrinsic {
				signed: alice(),
				index: 0,
				function: Call::Consensus(consensus::Call::remark(vec![0; 60000])),
			}]
		)
	}

	#[test]
	fn full_native_block_import_works() {
		let mut t = new_test_ext(false);

		executor().call(&mut t, 8, COMPACT_CODE, "execute_block", &block1(false).0, true).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 41);
			assert_eq!(Balances::total_balance(&bob()), 69);
			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: Event::balances(balances::RawEvent::NewAccount(bob(), 1, balances::NewAccountOutcome::NoHint))
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: Event::system(system::Event::ExtrinsicSuccess)
				}
			]);
		});

		executor().call(&mut t, 8, COMPACT_CODE, "execute_block", &block2().0, true).0.unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 30);
			assert_eq!(Balances::total_balance(&bob()), 78);
			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: Event::system(system::Event::ExtrinsicSuccess)
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(1),
					event: Event::system(system::Event::ExtrinsicSuccess)
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::session(session::RawEvent::NewSession(1))
				},
				EventRecord {
					phase: Phase::Finalization,
					event: Event::staking(staking::RawEvent::Reward(0))
				}
			]);
		});
	}

	#[test]
	fn full_wasm_block_import_works() {
		let mut t = new_test_ext(false);

		WasmExecutor::new().call(&mut t, 8, COMPACT_CODE, "execute_block", &block1(false).0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 41);
			assert_eq!(Balances::total_balance(&bob()), 69);
		});

		WasmExecutor::new().call(&mut t, 8, COMPACT_CODE, "execute_block", &block2().0).unwrap();

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 30);
			assert_eq!(Balances::total_balance(&bob()), 78);
		});
	}

	#[test]
	fn wasm_big_block_import_fails() {
		let mut t = new_test_ext(false);

		let r = WasmExecutor::new().call(&mut t, 8, COMPACT_CODE, "execute_block", &block1big().0);
		assert!(!r.is_ok());
	}

	#[test]
	fn native_big_block_import_succeeds() {
		let mut t = new_test_ext(false);

		let r = Executor::new().call(&mut t, 8, COMPACT_CODE, "execute_block", &block1big().0, true).0;
		assert!(r.is_ok());
	}

	#[test]
	fn native_big_block_import_fails_on_fallback() {
		let mut t = new_test_ext(false);

		let r = Executor::new().call(&mut t, 8, COMPACT_CODE, "execute_block", &block1big().0, false).0;
		assert!(!r.is_ok());
	}

	#[test]
	fn panic_execution_gives_error() {
		let mut t = TestExternalities::<KeccakHasher, RlpCodec>::new(map![
			twox_128(&<balances::FreeBalance<Concrete>>::key_for(alice())).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TotalIssuance<Concrete>>::key()).to_vec() => vec![69u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![70u8; 8],
			twox_128(<balances::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::ExistentialDeposit<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::TransferFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::NextEnumSet<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		]);

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.wasm");
		let r = WasmExecutor::new().call(&mut t, 8, &foreign_code[..], "initialise_block", &vec![].and(&from_block_number(1u64)));
		assert!(r.is_ok());
		let r = WasmExecutor::new().call(&mut t, 8, &foreign_code[..], "apply_extrinsic", &vec![].and(&xt())).unwrap();
		let r = ApplyResult::decode(&mut &r[..]).unwrap();
		assert_eq!(r, Err(ApplyError::CantPay));
	}

	#[test]
	fn successful_execution_gives_ok() {
		let mut t = TestExternalities::<KeccakHasher, RlpCodec>::new(map![
			twox_128(&<balances::FreeBalance<Concrete>>::key_for(alice())).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TotalIssuance<Concrete>>::key()).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0],
			twox_128(<balances::TransactionBaseFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::TransactionByteFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::ExistentialDeposit<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::TransferFee<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(<balances::NextEnumSet<Concrete>>::key()).to_vec() => vec![0u8; 8],
			twox_128(&<system::BlockHash<Concrete>>::key_for(0)).to_vec() => vec![0u8; 32]
		]);

		let foreign_code = include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/demo_runtime.compact.wasm");
		let r = WasmExecutor::new().call(&mut t, 8, &foreign_code[..], "initialise_block", &vec![].and(&from_block_number(1u64)));
		assert!(r.is_ok());
		let r = WasmExecutor::new().call(&mut t, 8, &foreign_code[..], "apply_extrinsic", &vec![].and(&xt())).unwrap();
		let r = ApplyResult::decode(&mut &r[..]).unwrap();
		assert_eq!(r, Ok(ApplyOutcome::Success));

		runtime_io::with_externalities(&mut t, || {
			assert_eq!(Balances::total_balance(&alice()), 42);
			assert_eq!(Balances::total_balance(&bob()), 69);
		});
	}

	#[test]
	fn full_native_block_import_works_with_changes_trie() {
		let mut t = new_test_ext(true);
		Executor::new().call(&mut t, 8, COMPACT_CODE, "execute_block", &block1(true).0, true).0.unwrap();

		assert!(t.storage_changes_root().is_some());
	}

	#[test]
	fn full_wasm_block_import_works_with_changes_trie() {
		let mut t = new_test_ext(true);
		WasmExecutor::new().call(&mut t, 8, COMPACT_CODE, "execute_block", &block1(true).0).unwrap();

		assert!(t.storage_changes_root().is_some());
	}
}
