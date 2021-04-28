// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Traits and associated utilities for use in the FRAME environment.
//!
//! NOTE: If you're looking for `parameter_types`, it has moved in to the top-level module.

pub mod tokens;
pub use tokens::fungible;
pub use tokens::fungibles;
pub use tokens::currency::{
	Currency, LockIdentifier, LockableCurrency, ReservableCurrency, VestingSchedule,
};
pub use tokens::imbalance::{Imbalance, OnUnbalanced, SignedImbalance};
pub use tokens::{ExistenceRequirement, WithdrawReasons, BalanceStatus};

<<<<<<< HEAD
/// Re-expected for the macro.
#[doc(hidden)]
pub use sp_std::{mem::{swap, take}, cell::RefCell, vec::Vec, boxed::Box};

/// A trait for online node inspection in a session.
///
/// Something that can give information about the current validator set.
pub trait ValidatorSet<AccountId> {
	/// Type for representing validator id in a session.
	type ValidatorId: Parameter;
	/// A type for converting `AccountId` to `ValidatorId`.
	type ValidatorIdOf: Convert<AccountId, Option<Self::ValidatorId>>;

	/// Returns current session index.
	fn session_index() -> SessionIndex;

	/// Returns the active set of validators.
	fn validators() -> Vec<Self::ValidatorId>;
}

/// [`ValidatorSet`] combined with an identification.
pub trait ValidatorSetWithIdentification<AccountId>: ValidatorSet<AccountId> {
	/// Full identification of `ValidatorId`.
	type Identification: Parameter;
	/// A type for converting `ValidatorId` to `Identification`.
	type IdentificationOf: Convert<Self::ValidatorId, Option<Self::Identification>>;
}

/// A session handler for specific key type.
pub trait OneSessionHandler<ValidatorId>: BoundToRuntimeAppPublic {
	/// The key type expected.
	type Key: Decode + Default + RuntimeAppPublic;

	/// The given validator set will be used for the genesis session.
	/// It is guaranteed that the given validator set will also be used
	/// for the second session, therefore the first call to `on_new_session`
	/// should provide the same validator set.
	fn on_genesis_session<'a, I: 'a>(validators: I)
		where I: Iterator<Item=(&'a ValidatorId, Self::Key)>, ValidatorId: 'a;

	/// Session set has changed; act appropriately. Note that this can be called
	/// before initialization of your module.
	///
	/// `changed` is true when at least one of the session keys
	/// or the underlying economic identities/distribution behind one the
	/// session keys has changed, false otherwise.
	///
	/// The `validators` are the validators of the incoming session, and `queued_validators`
	/// will follow.
	fn on_new_session<'a, I: 'a>(
		changed: bool,
		validators: I,
		queued_validators: I,
	) where I: Iterator<Item=(&'a ValidatorId, Self::Key)>, ValidatorId: 'a;

	/// A notification for end of the session.
	///
	/// Note it is triggered before any `SessionManager::end_session` handlers,
	/// so we can still affect the validator set.
	fn on_before_session_ending() {}

	/// A validator got disabled. Act accordingly until a new session begins.
	fn on_disabled(_validator_index: usize);
}

/// Simple trait for providing a filter over a reference to some type.
pub trait Filter<T> {
	/// Determine if a given value should be allowed through the filter (returns `true`) or not.
	fn filter(_: &T) -> bool;
}

impl<T> Filter<T> for () {
	fn filter(_: &T) -> bool { true }
}

/// Migrate a given account.
#[impl_trait_for_tuples::impl_for_tuples(30)]
pub trait MigrateAccount<A> {
	/// Migrate the `account`.
	fn migrate_account(account: &A);
}

/// Trait to add a constraint onto the filter.
pub trait FilterStack<T>: Filter<T> {
	/// The type used to archive the stack.
	type Stack;

	/// Add a new `constraint` onto the filter.
	fn push(constraint: impl Fn(&T) -> bool + 'static);

	/// Removes the most recently pushed, and not-yet-popped, constraint from the filter.
	fn pop();

	/// Clear the filter, returning a value that may be used later to `restore` it.
	fn take() -> Self::Stack;

	/// Restore the filter from a previous `take` operation.
	fn restore(taken: Self::Stack);
}

/// Guard type for pushing a constraint to a `FilterStack` and popping when dropped.
pub struct FilterStackGuard<F: FilterStack<T>, T>(PhantomData<(F, T)>);

/// Guard type for clearing all pushed constraints from a `FilterStack` and reinstating them when
/// dropped.
pub struct ClearFilterGuard<F: FilterStack<T>, T>(Option<F::Stack>, PhantomData<T>);

impl<F: FilterStack<T>, T> FilterStackGuard<F, T> {
	/// Create a new instance, adding a new `constraint` onto the filter `T`, and popping it when
	/// this instance is dropped.
	pub fn new(constraint: impl Fn(&T) -> bool + 'static) -> Self {
		F::push(constraint);
		Self(PhantomData)
	}
}

impl<F: FilterStack<T>, T> Drop for FilterStackGuard<F, T> {
	fn drop(&mut self) {
		F::pop();
	}
}

impl<F: FilterStack<T>, T> ClearFilterGuard<F, T> {
	/// Create a new instance, adding a new `constraint` onto the filter `T`, and popping it when
	/// this instance is dropped.
	pub fn new() -> Self {
		Self(Some(F::take()), PhantomData)
	}
}

impl<F: FilterStack<T>, T> Drop for ClearFilterGuard<F, T> {
	fn drop(&mut self) {
		if let Some(taken) = self.0.take() {
			F::restore(taken);
		}
	}
}

/// Simple trait for providing a filter over a reference to some type, given an instance of itself.
pub trait InstanceFilter<T>: Sized + Send + Sync {
	/// Determine if a given value should be allowed through the filter (returns `true`) or not.
	fn filter(&self, _: &T) -> bool;

	/// Determines whether `self` matches at least everything that `_o` does.
	fn is_superset(&self, _o: &Self) -> bool { false }
}

impl<T> InstanceFilter<T> for () {
	fn filter(&self, _: &T) -> bool { true }
	fn is_superset(&self, _o: &Self) -> bool { true }
}

#[macro_export]
macro_rules! impl_filter_stack {
	($target:ty, $base:ty, $call:ty, $module:ident) => {
		#[cfg(feature = "std")]
		mod $module {
			#[allow(unused_imports)]
			use super::*;
			use $crate::traits::{swap, take, RefCell, Vec, Box, Filter, FilterStack};

			thread_local! {
				static FILTER: RefCell<Vec<Box<dyn Fn(&$call) -> bool + 'static>>> = RefCell::new(Vec::new());
			}

			impl Filter<$call> for $target {
				fn filter(call: &$call) -> bool {
					<$base>::filter(call) &&
						FILTER.with(|filter| filter.borrow().iter().all(|f| f(call)))
				}
			}

			impl FilterStack<$call> for $target {
				type Stack = Vec<Box<dyn Fn(&$call) -> bool + 'static>>;
				fn push(f: impl Fn(&$call) -> bool + 'static) {
					FILTER.with(|filter| filter.borrow_mut().push(Box::new(f)));
				}
				fn pop() {
					FILTER.with(|filter| filter.borrow_mut().pop());
				}
				fn take() -> Self::Stack {
					FILTER.with(|filter| take(filter.borrow_mut().as_mut()))
				}
				fn restore(mut s: Self::Stack) {
					FILTER.with(|filter| swap(filter.borrow_mut().as_mut(), &mut s));
				}
			}
		}

		#[cfg(not(feature = "std"))]
		mod $module {
			#[allow(unused_imports)]
			use super::*;
			use $crate::traits::{swap, take, RefCell, Vec, Box, Filter, FilterStack};

			struct ThisFilter(RefCell<Vec<Box<dyn Fn(&$call) -> bool + 'static>>>);
			// NOTE: Safe only in wasm (guarded above) because there's only one thread.
			unsafe impl Send for ThisFilter {}
			unsafe impl Sync for ThisFilter {}

			static FILTER: ThisFilter = ThisFilter(RefCell::new(Vec::new()));

			impl Filter<$call> for $target {
				fn filter(call: &$call) -> bool {
					<$base>::filter(call) && FILTER.0.borrow().iter().all(|f| f(call))
				}
			}

			impl FilterStack<$call> for $target {
				type Stack = Vec<Box<dyn Fn(&$call) -> bool + 'static>>;
				fn push(f: impl Fn(&$call) -> bool + 'static) {
					FILTER.0.borrow_mut().push(Box::new(f));
				}
				fn pop() {
					FILTER.0.borrow_mut().pop();
				}
				fn take() -> Self::Stack {
					take(FILTER.0.borrow_mut().as_mut())
				}
				fn restore(mut s: Self::Stack) {
					swap(FILTER.0.borrow_mut().as_mut(), &mut s);
				}
			}
		}
	}
}

/// Type that provide some integrity tests.
///
/// This implemented for modules by `decl_module`.
#[impl_for_tuples(30)]
pub trait IntegrityTest {
	/// Run integrity test.
	///
	/// The test is not executed in a externalities provided environment.
	fn integrity_test() {}
}

#[cfg(test)]
mod test_impl_filter_stack {
	use super::*;

	pub struct IsCallable;
	pub struct BaseFilter;
	impl Filter<u32> for BaseFilter {
		fn filter(x: &u32) -> bool { x % 2 == 0 }
	}
	impl_filter_stack!(
		crate::traits::test_impl_filter_stack::IsCallable,
		crate::traits::test_impl_filter_stack::BaseFilter,
		u32,
		is_callable
	);

	#[test]
	fn impl_filter_stack_should_work() {
		assert!(IsCallable::filter(&36));
		assert!(IsCallable::filter(&40));
		assert!(IsCallable::filter(&42));
		assert!(!IsCallable::filter(&43));

		IsCallable::push(|x| *x < 42);
		assert!(IsCallable::filter(&36));
		assert!(IsCallable::filter(&40));
		assert!(!IsCallable::filter(&42));

		IsCallable::push(|x| *x % 3 == 0);
		assert!(IsCallable::filter(&36));
		assert!(!IsCallable::filter(&40));

		IsCallable::pop();
		assert!(IsCallable::filter(&36));
		assert!(IsCallable::filter(&40));
		assert!(!IsCallable::filter(&42));

		let saved = IsCallable::take();
		assert!(IsCallable::filter(&36));
		assert!(IsCallable::filter(&40));
		assert!(IsCallable::filter(&42));
		assert!(!IsCallable::filter(&43));

		IsCallable::restore(saved);
		assert!(IsCallable::filter(&36));
		assert!(IsCallable::filter(&40));
		assert!(!IsCallable::filter(&42));

		IsCallable::pop();
		assert!(IsCallable::filter(&36));
		assert!(IsCallable::filter(&40));
		assert!(IsCallable::filter(&42));
		assert!(!IsCallable::filter(&43));
	}

	#[test]
	fn guards_should_work() {
		assert!(IsCallable::filter(&36));
		assert!(IsCallable::filter(&40));
		assert!(IsCallable::filter(&42));
		assert!(!IsCallable::filter(&43));
		{
			let _guard_1 = FilterStackGuard::<IsCallable, u32>::new(|x| *x < 42);
			assert!(IsCallable::filter(&36));
			assert!(IsCallable::filter(&40));
			assert!(!IsCallable::filter(&42));
			{
				let _guard_2 = FilterStackGuard::<IsCallable, u32>::new(|x| *x % 3 == 0);
				assert!(IsCallable::filter(&36));
				assert!(!IsCallable::filter(&40));
			}
			assert!(IsCallable::filter(&36));
			assert!(IsCallable::filter(&40));
			assert!(!IsCallable::filter(&42));
			{
				let _guard_2 = ClearFilterGuard::<IsCallable, u32>::new();
				assert!(IsCallable::filter(&36));
				assert!(IsCallable::filter(&40));
				assert!(IsCallable::filter(&42));
				assert!(!IsCallable::filter(&43));
			}
			assert!(IsCallable::filter(&36));
			assert!(IsCallable::filter(&40));
			assert!(!IsCallable::filter(&42));
		}
		assert!(IsCallable::filter(&36));
		assert!(IsCallable::filter(&40));
		assert!(IsCallable::filter(&42));
		assert!(!IsCallable::filter(&43));
	}
}

/// An abstraction of a value stored within storage, but possibly as part of a larger composite
/// item.
pub trait StoredMap<K, T: Default> {
	/// Get the item, or its default if it doesn't yet exist; we make no distinction between the
	/// two.
	fn get(k: &K) -> T;

	/// Maybe mutate the item only if an `Ok` value is returned from `f`. Do nothing if an `Err` is
	/// returned. It is removed or reset to default value if it has been mutated to `None`
	fn try_mutate_exists<R, E: From<StoredMapError>>(
		k: &K,
		f: impl FnOnce(&mut Option<T>) -> Result<R, E>,
	) -> Result<R, E>;

	// Everything past here has a default implementation.

	/// Mutate the item.
	fn mutate<R>(k: &K, f: impl FnOnce(&mut T) -> R) -> Result<R, StoredMapError> {
		Self::mutate_exists(k, |maybe_account| match maybe_account {
			Some(ref mut account) => f(account),
			x @ None => {
				let mut account = Default::default();
				let r = f(&mut account);
				*x = Some(account);
				r
			}
		})
	}

	/// Mutate the item, removing or resetting to default value if it has been mutated to `None`.
	///
	/// This is infallible as long as the value does not get destroyed.
	fn mutate_exists<R>(
		k: &K,
		f: impl FnOnce(&mut Option<T>) -> R,
	) -> Result<R, StoredMapError> {
		Self::try_mutate_exists(k, |x| -> Result<R, StoredMapError> { Ok(f(x)) })
	}

	/// Set the item to something new.
	fn insert(k: &K, t: T) -> Result<(), StoredMapError> { Self::mutate(k, |i| *i = t) }

	/// Remove the item or otherwise replace it with its default value; we don't care which.
	fn remove(k: &K) -> Result<(), StoredMapError> { Self::mutate_exists(k, |x| *x = None) }
}

/// A simple, generic one-parameter event notifier/handler.
pub trait HandleLifetime<T> {
	/// An account was created.
	fn created(_t: &T) -> Result<(), StoredMapError> { Ok(()) }

	/// An account was killed.
	fn killed(_t: &T) -> Result<(), StoredMapError> { Ok(()) }
}

impl<T> HandleLifetime<T> for () {}

/// A shim for placing around a storage item in order to use it as a `StoredValue`. Ideally this
/// wouldn't be needed as `StorageValue`s should blanket implement `StoredValue`s, however this
/// would break the ability to have custom impls of `StoredValue`. The other workaround is to
/// implement it directly in the macro.
///
/// This form has the advantage that two additional types are provides, `Created` and `Removed`,
/// which are both generic events that can be tied to handlers to do something in the case of being
/// about to create an account where one didn't previously exist (at all; not just where it used to
/// be the default value), or where the account is being removed or reset back to the default value
/// where previously it did exist (though may have been in a default state). This works well with
/// system module's `CallOnCreatedAccount` and `CallKillAccount`.
pub struct StorageMapShim<S, L, K, T>(sp_std::marker::PhantomData<(S, L, K, T)>);
impl<
	S: StorageMap<K, T, Query=T>,
	L: HandleLifetime<K>,
	K: FullCodec,
	T: FullCodec + Default,
> StoredMap<K, T> for StorageMapShim<S, L, K, T> {
	fn get(k: &K) -> T { S::get(k) }
	fn insert(k: &K, t: T) -> Result<(), StoredMapError> {
		if !S::contains_key(&k) {
			L::created(k)?;
		}
		S::insert(k, t);
		Ok(())
	}
	fn remove(k: &K) -> Result<(), StoredMapError> {
		if S::contains_key(&k) {
			L::killed(&k)?;
			S::remove(k);
		}
		Ok(())
	}
	fn mutate<R>(k: &K, f: impl FnOnce(&mut T) -> R) -> Result<R, StoredMapError> {
		if !S::contains_key(&k) {
			L::created(k)?;
		}
		Ok(S::mutate(k, f))
	}
	fn mutate_exists<R>(k: &K, f: impl FnOnce(&mut Option<T>) -> R) -> Result<R, StoredMapError> {
		S::try_mutate_exists(k, |maybe_value| {
			let existed = maybe_value.is_some();
			let r = f(maybe_value);
			let exists = maybe_value.is_some();

			if !existed && exists {
				L::created(k)?;
			} else if existed && !exists {
				L::killed(k)?;
			}
			Ok(r)
		})
	}
	fn try_mutate_exists<R, E: From<StoredMapError>>(
		k: &K,
		f: impl FnOnce(&mut Option<T>) -> Result<R, E>,
	) -> Result<R, E> {
		S::try_mutate_exists(k, |maybe_value| {
			let existed = maybe_value.is_some();
			let r = f(maybe_value)?;
			let exists = maybe_value.is_some();

			if !existed && exists {
				L::created(k).map_err(E::from)?;
			} else if existed && !exists {
				L::killed(k).map_err(E::from)?;
			}
			Ok(r)
		})
	}
}

/// Something that can estimate at which block the next session rotation will happen (i.e. a new
/// session starts).
///
/// The accuracy of the estimates is dependent on the specific implementation, but in order to get
/// the best estimate possible these methods should be called throughout the duration of the session
/// (rather than calling once and storing the result).
///
/// This should be the same logical unit that dictates `ShouldEndSession` to the session module. No
/// assumptions are made about the scheduling of the sessions.
pub trait EstimateNextSessionRotation<BlockNumber> {
	/// Return the average length of a session.
	///
	/// This may or may not be accurate.
	fn average_session_length() -> BlockNumber;

	/// Return an estimate of the current session progress.
	///
	/// None should be returned if the estimation fails to come to an answer.
	fn estimate_current_session_progress(now: BlockNumber) -> (Option<Percent>, Weight);

	/// Return the block number at which the next session rotation is estimated to happen.
	///
	/// None should be returned if the estimation fails to come to an answer.
	fn estimate_next_session_rotation(now: BlockNumber) -> (Option<BlockNumber>, Weight);
}

impl<BlockNumber: Zero> EstimateNextSessionRotation<BlockNumber> for () {
	fn average_session_length() -> BlockNumber {
		Zero::zero()
	}

	fn estimate_current_session_progress(_: BlockNumber) -> (Option<Percent>, Weight) {
		(None, Zero::zero())
	}

	fn estimate_next_session_rotation(_: BlockNumber) -> (Option<BlockNumber>, Weight) {
		(None, Zero::zero())
	}
}

/// Something that can estimate at which block scheduling of the next session will happen (i.e when
/// we will try to fetch new validators).
///
/// This only refers to the point when we fetch the next session details and not when we enact them
/// (for enactment there's `EstimateNextSessionRotation`). With `pallet-session` this should be
/// triggered whenever `SessionManager::new_session` is called.
///
/// For example, if we are using a staking module this would be the block when the session module
/// would ask staking what the next validator set will be, as such this must always be implemented
/// by the session module.
pub trait EstimateNextNewSession<BlockNumber> {
	/// Return the average length of a session.
	///
	/// This may or may not be accurate.
	fn average_session_length() -> BlockNumber;

	/// Return the block number at which the next new session is estimated to happen.
	///
	/// None should be returned if the estimation fails to come to an answer.
	fn estimate_next_new_session(_: BlockNumber) -> (Option<BlockNumber>, Weight);
}

impl<BlockNumber: Zero> EstimateNextNewSession<BlockNumber> for () {
	fn average_session_length() -> BlockNumber {
		Zero::zero()
	}

	fn estimate_next_new_session(_: BlockNumber) -> (Option<BlockNumber>, Weight) {
		(None, Zero::zero())
	}
}

/// Anything that can have a `::len()` method.
pub trait Len {
	/// Return the length of data type.
	fn len(&self) -> usize;
}

impl<T: IntoIterator + Clone,> Len for T where <T as IntoIterator>::IntoIter: ExactSizeIterator {
	fn len(&self) -> usize {
		self.clone().into_iter().len()
	}
}

/// A trait for querying a single value from a type.
///
/// It is not required that the value is constant.
pub trait Get<T> {
	/// Return the current value.
	fn get() -> T;
}

impl<T: Default> Get<T> for () {
	fn get() -> T { T::default() }
}

/// A trait for querying whether a type can be said to "contain" a value.
pub trait Contains<T: Ord> {
	/// Return `true` if this "contains" the given value `t`.
	fn contains(t: &T) -> bool { Self::sorted_members().binary_search(t).is_ok() }

	/// Get a vector of all members in the set, ordered.
	fn sorted_members() -> Vec<T>;

	/// Get the number of items in the set.
	fn count() -> usize { Self::sorted_members().len() }

	/// Add an item that would satisfy `contains`. It does not make sure any other
	/// state is correctly maintained or generated.
	///
	/// **Should be used for benchmarking only!!!**
	#[cfg(feature = "runtime-benchmarks")]
	fn add(_t: &T) { unimplemented!() }
}

/// A trait for querying bound for the length of an implementation of `Contains`
pub trait ContainsLengthBound {
	/// Minimum number of elements contained
	fn min_len() -> usize;
	/// Maximum number of elements contained
	fn max_len() -> usize;
}

/// Handler for when a new account has been created.
#[impl_for_tuples(30)]
pub trait OnNewAccount<AccountId> {
	/// A new account `who` has been registered.
	fn on_new_account(who: &AccountId);
}

/// The account with the given id was reaped.
#[impl_for_tuples(30)]
pub trait OnKilledAccount<AccountId> {
	/// The account with the given id was reaped.
	fn on_killed_account(who: &AccountId);
}

/// A trait for finding the author of a block header based on the `PreRuntime` digests contained
/// within it.
pub trait FindAuthor<Author> {
	/// Find the author of a block based on the pre-runtime digests.
	fn find_author<'a, I>(digests: I) -> Option<Author>
		where I: 'a + IntoIterator<Item=(ConsensusEngineId, &'a [u8])>;
}

impl<A> FindAuthor<A> for () {
	fn find_author<'a, I>(_: I) -> Option<A>
		where I: 'a + IntoIterator<Item=(ConsensusEngineId, &'a [u8])>
	{
		None
	}
}

/// A trait for verifying the seal of a header and returning the author.
pub trait VerifySeal<Header, Author> {
	/// Verify a header and return the author, if any.
	fn verify_seal(header: &Header) -> Result<Option<Author>, &'static str>;
}

/// Something which can compute and check proofs of
/// a historical key owner and return full identification data of that
/// key owner.
pub trait KeyOwnerProofSystem<Key> {
	/// The proof of membership itself.
	type Proof: Codec;
	/// The full identification of a key owner and the stash account.
	type IdentificationTuple: Codec;

	/// Prove membership of a key owner in the current block-state.
	///
	/// This should typically only be called off-chain, since it may be
	/// computationally heavy.
	///
	/// Returns `Some` iff the key owner referred to by the given `key` is a
	/// member of the current set.
	fn prove(key: Key) -> Option<Self::Proof>;

	/// Check a proof of membership on-chain. Return `Some` iff the proof is
	/// valid and recent enough to check.
	fn check_proof(key: Key, proof: Self::Proof) -> Option<Self::IdentificationTuple>;
}

impl<Key> KeyOwnerProofSystem<Key> for () {
	// The proof and identification tuples is any bottom type to guarantee that the methods of this
	// implementation can never be called or return anything other than `None`.
	type Proof = crate::Void;
	type IdentificationTuple = crate::Void;

	fn prove(_key: Key) -> Option<Self::Proof> {
		None
	}

	fn check_proof(_key: Key, _proof: Self::Proof) -> Option<Self::IdentificationTuple> {
		None
	}
}

/// Handler for when some currency "account" decreased in balance for
/// some reason.
///
/// The only reason at present for an increase would be for validator rewards, but
/// there may be other reasons in the future or for other chains.
///
/// Reasons for decreases include:
///
/// - Someone got slashed.
/// - Someone paid for a transaction to be included.
pub trait OnUnbalanced<Imbalance: TryDrop> {
	/// Handler for some imbalances. The different imbalances might have different origins or
	/// meanings, dependent on the context. Will default to simply calling on_unbalanced for all
	/// of them. Infallible.
	fn on_unbalanceds<B>(amounts: impl Iterator<Item=Imbalance>) where Imbalance: crate::traits::Imbalance<B> {
		Self::on_unbalanced(amounts.fold(Imbalance::zero(), |i, x| x.merge(i)))
	}

	/// Handler for some imbalance. Infallible.
	fn on_unbalanced(amount: Imbalance) {
		amount.try_drop().unwrap_or_else(Self::on_nonzero_unbalanced)
	}

	/// Actually handle a non-zero imbalance. You probably want to implement this rather than
	/// `on_unbalanced`.
	fn on_nonzero_unbalanced(amount: Imbalance) { drop(amount); }
}

impl<Imbalance: TryDrop> OnUnbalanced<Imbalance> for () {}

/// Simple boolean for whether an account needs to be kept in existence.
#[derive(Copy, Clone, Eq, PartialEq)]
pub enum ExistenceRequirement {
	/// Operation must not result in the account going out of existence.
	///
	/// Note this implies that if the account never existed in the first place, then the operation
	/// may legitimately leave the account unchanged and still non-existent.
	KeepAlive,
	/// Operation may result in account going out of existence.
	AllowDeath,
}

/// A type for which some values make sense to be able to drop without further consideration.
pub trait TryDrop: Sized {
	/// Drop an instance cleanly. Only works if its value represents "no-operation".
	fn try_drop(self) -> Result<(), Self>;
}

/// A trait for a not-quite Linear Type that tracks an imbalance.
///
/// Functions that alter account balances return an object of this trait to
/// express how much account balances have been altered in aggregate. If
/// dropped, the currency system will take some default steps to deal with
/// the imbalance (`balances` module simply reduces or increases its
/// total issuance). Your module should generally handle it in some way,
/// good practice is to do so in a configurable manner using an
/// `OnUnbalanced` type for each situation in which your module needs to
/// handle an imbalance.
///
/// Imbalances can either be Positive (funds were added somewhere without
/// being subtracted elsewhere - e.g. a reward) or Negative (funds deducted
/// somewhere without an equal and opposite addition - e.g. a slash or
/// system fee payment).
///
/// Since they are unsigned, the actual type is always Positive or Negative.
/// The trait makes no distinction except to define the `Opposite` type.
///
/// New instances of zero value can be created (`zero`) and destroyed
/// (`drop_zero`).
///
/// Existing instances can be `split` and merged either consuming `self` with
/// `merge` or mutating `self` with `subsume`. If the target is an `Option`,
/// then `maybe_merge` and `maybe_subsume` might work better. Instances can
/// also be `offset` with an `Opposite` that is less than or equal to in value.
///
/// You can always retrieve the raw balance value using `peek`.
#[must_use]
pub trait Imbalance<Balance>: Sized + TryDrop {
	/// The oppositely imbalanced type. They come in pairs.
	type Opposite: Imbalance<Balance>;

	/// The zero imbalance. Can be destroyed with `drop_zero`.
	fn zero() -> Self;

	/// Drop an instance cleanly. Only works if its `self.value()` is zero.
	fn drop_zero(self) -> Result<(), Self>;

	/// Consume `self` and return two independent instances; the first
	/// is guaranteed to be at most `amount` and the second will be the remainder.
	fn split(self, amount: Balance) -> (Self, Self);

	/// Consume `self` and return two independent instances; the amounts returned will be in
	/// approximately the same ratio as `first`:`second`.
	///
	/// NOTE: This requires up to `first + second` room for a multiply, and `first + second` should
	/// fit into a `u32`. Overflow will safely saturate in both cases.
	fn ration(self, first: u32, second: u32) -> (Self, Self)
		where Balance: From<u32> + Saturating + Div<Output=Balance>
	{
		let total: u32 = first.saturating_add(second);
		let amount1 = self.peek().saturating_mul(first.into()) / total.into();
		self.split(amount1)
	}

	/// Consume self and add its two components, defined by the first component's balance,
	/// element-wise to two pre-existing Imbalances.
	///
	/// A convenient replacement for `split` and `merge`.
	fn split_merge(self, amount: Balance, others: (Self, Self)) -> (Self, Self) {
		let (a, b) = self.split(amount);
		(a.merge(others.0), b.merge(others.1))
	}

	/// Consume self and add its two components, defined by the ratio `first`:`second`,
	/// element-wise to two pre-existing Imbalances.
	///
	/// A convenient replacement for `split` and `merge`.
	fn ration_merge(self, first: u32, second: u32, others: (Self, Self)) -> (Self, Self)
		where Balance: From<u32> + Saturating + Div<Output=Balance>
	{
		let (a, b) = self.ration(first, second);
		(a.merge(others.0), b.merge(others.1))
	}

	/// Consume self and add its two components, defined by the first component's balance,
	/// element-wise into two pre-existing Imbalance refs.
	///
	/// A convenient replacement for `split` and `subsume`.
	fn split_merge_into(self, amount: Balance, others: &mut (Self, Self)) {
		let (a, b) = self.split(amount);
		others.0.subsume(a);
		others.1.subsume(b);
	}

	/// Consume self and add its two components, defined by the ratio `first`:`second`,
	/// element-wise to two pre-existing Imbalances.
	///
	/// A convenient replacement for `split` and `merge`.
	fn ration_merge_into(self, first: u32, second: u32, others: &mut (Self, Self))
		where Balance: From<u32> + Saturating + Div<Output=Balance>
	{
		let (a, b) = self.ration(first, second);
		others.0.subsume(a);
		others.1.subsume(b);
	}

	/// Consume `self` and an `other` to return a new instance that combines
	/// both.
	fn merge(self, other: Self) -> Self;

	/// Consume self to mutate `other` so that it combines both. Just like `subsume`, only with
	/// reversed arguments.
	fn merge_into(self, other: &mut Self) {
		other.subsume(self)
	}

	/// Consume `self` and maybe an `other` to return a new instance that combines
	/// both.
	fn maybe_merge(self, other: Option<Self>) -> Self {
		if let Some(o) = other {
			self.merge(o)
		} else {
			self
		}
	}

	/// Consume an `other` to mutate `self` into a new instance that combines
	/// both.
	fn subsume(&mut self, other: Self);

	/// Maybe consume an `other` to mutate `self` into a new instance that combines
	/// both.
	fn maybe_subsume(&mut self, other: Option<Self>) {
		if let Some(o) = other {
			self.subsume(o)
		}
	}

	/// Consume self and along with an opposite counterpart to return
	/// a combined result.
	///
	/// Returns `Ok` along with a new instance of `Self` if this instance has a
	/// greater value than the `other`. Otherwise returns `Err` with an instance of
	/// the `Opposite`. In both cases the value represents the combination of `self`
	/// and `other`.
	fn offset(self, other: Self::Opposite) -> Result<Self, Self::Opposite>;

	/// The raw value of self.
	fn peek(&self) -> Balance;
}

/// Either a positive or a negative imbalance.
pub enum SignedImbalance<B, P: Imbalance<B>>{
	/// A positive imbalance (funds have been created but none destroyed).
	Positive(P),
	/// A negative imbalance (funds have been destroyed but none created).
	Negative(P::Opposite),
}

impl<
	P: Imbalance<B, Opposite=N>,
	N: Imbalance<B, Opposite=P>,
	B: AtLeast32BitUnsigned + FullCodec + Copy + MaybeSerializeDeserialize + Debug + Default,
> SignedImbalance<B, P> {
	pub fn zero() -> Self {
		SignedImbalance::Positive(P::zero())
	}

	pub fn drop_zero(self) -> Result<(), Self> {
		match self {
			SignedImbalance::Positive(x) => x.drop_zero().map_err(SignedImbalance::Positive),
			SignedImbalance::Negative(x) => x.drop_zero().map_err(SignedImbalance::Negative),
		}
	}

	/// Consume `self` and an `other` to return a new instance that combines
	/// both.
	pub fn merge(self, other: Self) -> Self {
		match (self, other) {
			(SignedImbalance::Positive(one), SignedImbalance::Positive(other)) =>
				SignedImbalance::Positive(one.merge(other)),
			(SignedImbalance::Negative(one), SignedImbalance::Negative(other)) =>
				SignedImbalance::Negative(one.merge(other)),
			(SignedImbalance::Positive(one), SignedImbalance::Negative(other)) =>
				if one.peek() > other.peek() {
					SignedImbalance::Positive(one.offset(other).ok().unwrap_or_else(P::zero))
				} else {
					SignedImbalance::Negative(other.offset(one).ok().unwrap_or_else(N::zero))
				},
			(one, other) => other.merge(one),
		}
	}
}

/// Split an unbalanced amount two ways between a common divisor.
pub struct SplitTwoWays<
	Balance,
	Imbalance,
	Part1,
	Target1,
	Part2,
	Target2,
>(PhantomData<(Balance, Imbalance, Part1, Target1, Part2, Target2)>);

impl<
	Balance: From<u32> + Saturating + Div<Output=Balance>,
	I: Imbalance<Balance>,
	Part1: U32,
	Target1: OnUnbalanced<I>,
	Part2: U32,
	Target2: OnUnbalanced<I>,
> OnUnbalanced<I> for SplitTwoWays<Balance, I, Part1, Target1, Part2, Target2>
{
	fn on_nonzero_unbalanced(amount: I) {
		let total: u32 = Part1::VALUE + Part2::VALUE;
		let amount1 = amount.peek().saturating_mul(Part1::VALUE.into()) / total.into();
		let (imb1, imb2) = amount.split(amount1);
		Target1::on_unbalanced(imb1);
		Target2::on_unbalanced(imb2);
	}
}

/// Abstraction over a fungible assets system.
pub trait Currency<AccountId> {
	/// The balance of an account.
	type Balance: AtLeast32BitUnsigned + FullCodec + Copy + MaybeSerializeDeserialize + Debug +
		Default;

	/// The opaque token type for an imbalance. This is returned by unbalanced operations
	/// and must be dealt with. It may be dropped but cannot be cloned.
	type PositiveImbalance: Imbalance<Self::Balance, Opposite=Self::NegativeImbalance>;

	/// The opaque token type for an imbalance. This is returned by unbalanced operations
	/// and must be dealt with. It may be dropped but cannot be cloned.
	type NegativeImbalance: Imbalance<Self::Balance, Opposite=Self::PositiveImbalance>;

	// PUBLIC IMMUTABLES

	/// The combined balance of `who`.
	fn total_balance(who: &AccountId) -> Self::Balance;

	/// Same result as `slash(who, value)` (but without the side-effects) assuming there are no
	/// balance changes in the meantime and only the reserved balance is not taken into account.
	fn can_slash(who: &AccountId, value: Self::Balance) -> bool;

	/// The total amount of issuance in the system.
	fn total_issuance() -> Self::Balance;

	/// The minimum balance any single account may have. This is equivalent to the `Balances` module's
	/// `ExistentialDeposit`.
	fn minimum_balance() -> Self::Balance;

	/// Reduce the total issuance by `amount` and return the according imbalance. The imbalance will
	/// typically be used to reduce an account by the same amount with e.g. `settle`.
	///
	/// This is infallible, but doesn't guarantee that the entire `amount` is burnt, for example
	/// in the case of underflow.
	fn burn(amount: Self::Balance) -> Self::PositiveImbalance;

	/// Increase the total issuance by `amount` and return the according imbalance. The imbalance
	/// will typically be used to increase an account by the same amount with e.g.
	/// `resolve_into_existing` or `resolve_creating`.
	///
	/// This is infallible, but doesn't guarantee that the entire `amount` is issued, for example
	/// in the case of overflow.
	fn issue(amount: Self::Balance) -> Self::NegativeImbalance;

	/// Produce a pair of imbalances that cancel each other out exactly.
	///
	/// This is just the same as burning and issuing the same amount and has no effect on the
	/// total issuance.
	fn pair(amount: Self::Balance) -> (Self::PositiveImbalance, Self::NegativeImbalance) {
		(Self::burn(amount.clone()), Self::issue(amount))
	}

	/// The 'free' balance of a given account.
	///
	/// This is the only balance that matters in terms of most operations on tokens. It alone
	/// is used to determine the balance when in the contract execution environment. When this
	/// balance falls below the value of `ExistentialDeposit`, then the 'current account' is
	/// deleted: specifically `FreeBalance`.
	///
	/// `system::AccountNonce` is also deleted if `ReservedBalance` is also zero (it also gets
	/// collapsed to zero if it ever becomes less than `ExistentialDeposit`.
	fn free_balance(who: &AccountId) -> Self::Balance;

	/// Returns `Ok` iff the account is able to make a withdrawal of the given amount
	/// for the given reason. Basically, it's just a dry-run of `withdraw`.
	///
	/// `Err(...)` with the reason why not otherwise.
	fn ensure_can_withdraw(
		who: &AccountId,
		_amount: Self::Balance,
		reasons: WithdrawReasons,
		new_balance: Self::Balance,
	) -> DispatchResult;

	// PUBLIC MUTABLES (DANGEROUS)

	/// Transfer some liquid free balance to another staker.
	///
	/// This is a very high-level function. It will ensure all appropriate fees are paid
	/// and no imbalance in the system remains.
	fn transfer(
		source: &AccountId,
		dest: &AccountId,
		value: Self::Balance,
		existence_requirement: ExistenceRequirement,
	) -> DispatchResult;

	/// Deducts up to `value` from the combined balance of `who`, preferring to deduct from the
	/// free balance. This function cannot fail.
	///
	/// The resulting imbalance is the first item of the tuple returned.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then a non-zero second item will be returned.
	fn slash(
		who: &AccountId,
		value: Self::Balance
	) -> (Self::NegativeImbalance, Self::Balance);

	/// Mints `value` to the free balance of `who`.
	///
	/// If `who` doesn't exist, nothing is done and an Err returned.
	fn deposit_into_existing(
		who: &AccountId,
		value: Self::Balance
	) -> result::Result<Self::PositiveImbalance, DispatchError>;

	/// Similar to deposit_creating, only accepts a `NegativeImbalance` and returns nothing on
	/// success.
	fn resolve_into_existing(
		who: &AccountId,
		value: Self::NegativeImbalance,
	) -> result::Result<(), Self::NegativeImbalance> {
		let v = value.peek();
		match Self::deposit_into_existing(who, v) {
			Ok(opposite) => Ok(drop(value.offset(opposite))),
			_ => Err(value),
		}
	}

	/// Adds up to `value` to the free balance of `who`. If `who` doesn't exist, it is created.
	///
	/// Infallible.
	fn deposit_creating(
		who: &AccountId,
		value: Self::Balance,
	) -> Self::PositiveImbalance;

	/// Similar to deposit_creating, only accepts a `NegativeImbalance` and returns nothing on
	/// success.
	fn resolve_creating(
		who: &AccountId,
		value: Self::NegativeImbalance,
	) {
		let v = value.peek();
		drop(value.offset(Self::deposit_creating(who, v)));
	}

	/// Removes some free balance from `who` account for `reason` if possible. If `liveness` is
	/// `KeepAlive`, then no less than `ExistentialDeposit` must be left remaining.
	///
	/// This checks any locks, vesting, and liquidity requirements. If the removal is not possible,
	/// then it returns `Err`.
	///
	/// If the operation is successful, this will return `Ok` with a `NegativeImbalance` whose value
	/// is `value`.
	fn withdraw(
		who: &AccountId,
		value: Self::Balance,
		reasons: WithdrawReasons,
		liveness: ExistenceRequirement,
	) -> result::Result<Self::NegativeImbalance, DispatchError>;

	/// Similar to withdraw, only accepts a `PositiveImbalance` and returns nothing on success.
	fn settle(
		who: &AccountId,
		value: Self::PositiveImbalance,
		reasons: WithdrawReasons,
		liveness: ExistenceRequirement,
	) -> result::Result<(), Self::PositiveImbalance> {
		let v = value.peek();
		match Self::withdraw(who, v, reasons, liveness) {
			Ok(opposite) => Ok(drop(value.offset(opposite))),
			_ => Err(value),
		}
	}

	/// Ensure an account's free balance equals some value; this will create the account
	/// if needed.
	///
	/// Returns a signed imbalance and status to indicate if the account was successfully updated or update
	/// has led to killing of the account.
	fn make_free_balance_be(
		who: &AccountId,
		balance: Self::Balance,
	) -> SignedImbalance<Self::Balance, Self::PositiveImbalance>;
}

/// Status of funds.
#[derive(PartialEq, Eq, Clone, Copy, Encode, Decode, RuntimeDebug)]
pub enum BalanceStatus {
	/// Funds are free, as corresponding to `free` item in Balances.
	Free,
	/// Funds are reserved, as corresponding to `reserved` item in Balances.
	Reserved,
}

/// A currency where funds can be reserved from the user.
pub trait ReservableCurrency<AccountId>: Currency<AccountId> {
	/// Same result as `reserve(who, value)` (but without the side-effects) assuming there
	/// are no balance changes in the meantime.
	fn can_reserve(who: &AccountId, value: Self::Balance) -> bool;

	/// Deducts up to `value` from reserved balance of `who`. This function cannot fail.
	///
	/// As much funds up to `value` will be deducted as possible. If the reserve balance of `who`
	/// is less than `value`, then a non-zero second item will be returned.
	fn slash_reserved(
		who: &AccountId,
		value: Self::Balance
	) -> (Self::NegativeImbalance, Self::Balance);

	/// The amount of the balance of a given account that is externally reserved; this can still get
	/// slashed, but gets slashed last of all.
	///
	/// This balance is a 'reserve' balance that other subsystems use in order to set aside tokens
	/// that are still 'owned' by the account holder, but which are suspendable.
	///
	/// When this balance falls below the value of `ExistentialDeposit`, then this 'reserve account'
	/// is deleted: specifically, `ReservedBalance`.
	///
	/// `system::AccountNonce` is also deleted if `FreeBalance` is also zero (it also gets
	/// collapsed to zero if it ever becomes less than `ExistentialDeposit`.
	fn reserved_balance(who: &AccountId) -> Self::Balance;

	/// Moves `value` from balance to reserved balance.
	///
	/// If the free balance is lower than `value`, then no funds will be moved and an `Err` will
	/// be returned to notify of this. This is different behavior than `unreserve`.
	fn reserve(who: &AccountId, value: Self::Balance) -> DispatchResult;

	/// Moves up to `value` from reserved balance to free balance. This function cannot fail.
	///
	/// As much funds up to `value` will be moved as possible. If the reserve balance of `who`
	/// is less than `value`, then the remaining amount will be returned.
	///
	/// # NOTES
	///
	/// - This is different from `reserve`.
	/// - If the remaining reserved balance is less than `ExistentialDeposit`, it will
	/// invoke `on_reserved_too_low` and could reap the account.
	fn unreserve(who: &AccountId, value: Self::Balance) -> Self::Balance;

	/// Moves up to `value` from reserved balance of account `slashed` to balance of account
	/// `beneficiary`. `beneficiary` must exist for this to succeed. If it does not, `Err` will be
	/// returned. Funds will be placed in either the `free` balance or the `reserved` balance,
	/// depending on the `status`.
	///
	/// As much funds up to `value` will be deducted as possible. If this is less than `value`,
	/// then `Ok(non_zero)` will be returned.
	fn repatriate_reserved(
		slashed: &AccountId,
		beneficiary: &AccountId,
		value: Self::Balance,
		status: BalanceStatus,
	) -> result::Result<Self::Balance, DispatchError>;
}

/// An identifier for a lock. Used for disambiguating different locks so that
/// they can be individually replaced or removed.
pub type LockIdentifier = [u8; 8];

/// A currency whose accounts can have liquidity restrictions.
pub trait LockableCurrency<AccountId>: Currency<AccountId> {
	/// The quantity used to denote time; usually just a `BlockNumber`.
	type Moment;

	/// The maximum number of locks a user should have on their account.
	type MaxLocks: Get<u32>;

	/// Create a new balance lock on account `who`.
	///
	/// If the new lock is valid (i.e. not already expired), it will push the struct to
	/// the `Locks` vec in storage. Note that you can lock more funds than a user has.
	///
	/// If the lock `id` already exists, this will update it.
	fn set_lock(
		id: LockIdentifier,
		who: &AccountId,
		amount: Self::Balance,
		reasons: WithdrawReasons,
	);

	/// Changes a balance lock (selected by `id`) so that it becomes less liquid in all
	/// parameters or creates a new one if it does not exist.
	///
	/// Calling `extend_lock` on an existing lock `id` differs from `set_lock` in that it
	/// applies the most severe constraints of the two, while `set_lock` replaces the lock
	/// with the new parameters. As in, `extend_lock` will set:
	/// - maximum `amount`
	/// - bitwise mask of all `reasons`
	fn extend_lock(
		id: LockIdentifier,
		who: &AccountId,
		amount: Self::Balance,
		reasons: WithdrawReasons,
	);

	/// Remove an existing lock.
	fn remove_lock(
		id: LockIdentifier,
		who: &AccountId,
	);
}

/// A vesting schedule over a currency. This allows a particular currency to have vesting limits
/// applied to it.
pub trait VestingSchedule<AccountId> {
	/// The quantity used to denote time; usually just a `BlockNumber`.
	type Moment;

	/// The currency that this schedule applies to.
	type Currency: Currency<AccountId>;

	/// Get the amount that is currently being vested and cannot be transferred out of this account.
	/// Returns `None` if the account has no vesting schedule.
	fn vesting_balance(who: &AccountId) -> Option<<Self::Currency as Currency<AccountId>>::Balance>;

	/// Adds a vesting schedule to a given account.
	///
	/// If there already exists a vesting schedule for the given account, an `Err` is returned
	/// and nothing is updated.
	///
	/// Is a no-op if the amount to be vested is zero.
	///
	/// NOTE: This doesn't alter the free balance of the account.
	fn add_vesting_schedule(
		who: &AccountId,
		locked: <Self::Currency as Currency<AccountId>>::Balance,
		per_block: <Self::Currency as Currency<AccountId>>::Balance,
		starting_block: Self::Moment,
	) -> DispatchResult;

	/// Remove a vesting schedule for a given account.
	///
	/// NOTE: This doesn't alter the free balance of the account.
	fn remove_vesting_schedule(who: &AccountId);
}

bitflags! {
	/// Reasons for moving funds out of an account.
	#[derive(Encode, Decode)]
	pub struct WithdrawReasons: i8 {
		/// In order to pay for (system) transaction costs.
		const TRANSACTION_PAYMENT = 0b00000001;
		/// In order to transfer ownership.
		const TRANSFER = 0b00000010;
		/// In order to reserve some funds for a later return or repatriation.
		const RESERVE = 0b00000100;
		/// In order to pay some other (higher-level) fees.
		const FEE = 0b00001000;
		/// In order to tip a validator for transaction inclusion.
		const TIP = 0b00010000;
	}
}

impl WithdrawReasons {
	/// Choose all variants except for `one`.
	///
	/// ```rust
	/// # use frame_support::traits::WithdrawReasons;
	/// # fn main() {
	/// assert_eq!(
	/// 	WithdrawReasons::FEE | WithdrawReasons::TRANSFER | WithdrawReasons::RESERVE | WithdrawReasons::TIP,
	/// 	WithdrawReasons::except(WithdrawReasons::TRANSACTION_PAYMENT),
	///	);
	/// # }
	/// ```
	pub fn except(one: WithdrawReasons) -> WithdrawReasons {
		let mut flags = Self::all();
		flags.toggle(one);
		flags
	}
}

pub trait Time {
	type Moment: AtLeast32Bit + Parameter + Default + Copy;

	fn now() -> Self::Moment;
}

/// Trait to deal with unix time.
pub trait UnixTime {
	/// Return duration since `SystemTime::UNIX_EPOCH`.
	fn now() -> core::time::Duration;
}

/// Trait for type that can handle incremental changes to a set of account IDs.
pub trait ChangeMembers<AccountId: Clone + Ord> {
	/// A number of members `incoming` just joined the set and replaced some `outgoing` ones. The
	/// new set is given by `new`, and need not be sorted.
	///
	/// This resets any previous value of prime.
	fn change_members(incoming: &[AccountId], outgoing: &[AccountId], mut new: Vec<AccountId>) {
		new.sort();
		Self::change_members_sorted(incoming, outgoing, &new[..]);
	}

	/// A number of members `_incoming` just joined the set and replaced some `_outgoing` ones. The
	/// new set is thus given by `sorted_new` and **must be sorted**.
	///
	/// NOTE: This is the only function that needs to be implemented in `ChangeMembers`.
	///
	/// This resets any previous value of prime.
	fn change_members_sorted(
		incoming: &[AccountId],
		outgoing: &[AccountId],
		sorted_new: &[AccountId],
	);

	/// Set the new members; they **must already be sorted**. This will compute the diff and use it to
	/// call `change_members_sorted`.
	///
	/// This resets any previous value of prime.
	fn set_members_sorted(new_members: &[AccountId], old_members: &[AccountId]) {
		let (incoming, outgoing) = Self::compute_members_diff_sorted(new_members, old_members);
		Self::change_members_sorted(&incoming[..], &outgoing[..], &new_members);
	}

	/// Compute diff between new and old members; they **must already be sorted**.
	///
	/// Returns incoming and outgoing members.
	fn compute_members_diff_sorted(
		new_members: &[AccountId],
		old_members: &[AccountId],
	) -> (Vec<AccountId>, Vec<AccountId>) {
		let mut old_iter = old_members.iter();
		let mut new_iter = new_members.iter();
		let mut incoming = Vec::new();
		let mut outgoing = Vec::new();
		let mut old_i = old_iter.next();
		let mut new_i = new_iter.next();
		loop {
			match (old_i, new_i) {
				(None, None) => break,
				(Some(old), Some(new)) if old == new => {
					old_i = old_iter.next();
					new_i = new_iter.next();
				}
				(Some(old), Some(new)) if old < new => {
					outgoing.push(old.clone());
					old_i = old_iter.next();
				}
				(Some(old), None) => {
					outgoing.push(old.clone());
					old_i = old_iter.next();
				}
				(_, Some(new)) => {
					incoming.push(new.clone());
					new_i = new_iter.next();
				}
			}
		}
		(incoming, outgoing)
	}

	/// Set the prime member.
	fn set_prime(_prime: Option<AccountId>) {}

	/// Get the current prime.
	fn get_prime() -> Option<AccountId> {
		None
	}
}

impl<T: Clone + Ord> ChangeMembers<T> for () {
	fn change_members(_: &[T], _: &[T], _: Vec<T>) {}
	fn change_members_sorted(_: &[T], _: &[T], _: &[T]) {}
	fn set_members_sorted(_: &[T], _: &[T]) {}
	fn set_prime(_: Option<T>) {}
}

/// Trait for type that can handle the initialization of account IDs at genesis.
pub trait InitializeMembers<AccountId> {
	/// Initialize the members to the given `members`.
	fn initialize_members(members: &[AccountId]);
}

impl<T> InitializeMembers<T> for () {
	fn initialize_members(_: &[T]) {}
}

/// A trait that is able to provide randomness.
///
/// Being a deterministic blockchain, real randomness is difficult to come by, different
/// implementations of this trait will provide different security guarantees. At best,
/// this will be randomness which was hard to predict a long time ago, but that has become
/// easy to predict recently.
pub trait Randomness<Output, BlockNumber> {
	/// Get the most recently determined random seed, along with the time in the past
	/// since when it was determinable by chain observers.
	///
	/// `subject` is a context identifier and allows you to get a different result to
	/// other callers of this function; use it like `random(&b"my context"[..])`.
	///
	/// NOTE: The returned seed should only be used to distinguish commitments made before
	/// the returned block number. If the block number is too early (i.e. commitments were
	/// made afterwards), then ensure no further commitments may be made and repeatedly
	/// call this on later blocks until the block number returned is later than the latest
	/// commitment.
	fn random(subject: &[u8]) -> (Output, BlockNumber);

	/// Get the basic random seed.
	///
	/// In general you won't want to use this, but rather `Self::random` which allows
	/// you to give a subject for the random result and whose value will be
	/// independently low-influence random from any other such seeds.
	///
	/// NOTE: The returned seed should only be used to distinguish commitments made before
	/// the returned block number. If the block number is too early (i.e. commitments were
	/// made afterwards), then ensure no further commitments may be made and repeatedly
	/// call this on later blocks until the block number returned is later than the latest
	/// commitment.
	fn random_seed() -> (Output, BlockNumber) {
		Self::random(&[][..])
	}
}

/// Trait to be used by block producing consensus engine modules to determine
/// how late the current block is (e.g. in a slot-based proposal mechanism how
/// many slots were skipped since the previous block).
pub trait Lateness<N> {
	/// Returns a generic measure of how late the current block is compared to
	/// its parent.
	fn lateness(&self) -> N;
}

impl<N: Zero> Lateness<N> for () {
	fn lateness(&self) -> N {
		Zero::zero()
	}
}

/// Implementors of this trait provide information about whether or not some validator has
/// been registered with them. The [Session module](../../pallet_session/index.html) is an implementor.
pub trait ValidatorRegistration<ValidatorId> {
	/// Returns true if the provided validator ID has been registered with the implementing runtime
	/// module
	fn is_registered(id: &ValidatorId) -> bool;
}

/// Provides information about the pallet setup in the runtime.
///
/// An implementor should be able to provide information about each pallet that
/// is configured in `construct_runtime!`.
pub trait PalletInfo {
	/// Convert the given pallet `P` into its index as configured in the runtime.
	fn index<P: 'static>() -> Option<usize>;
	/// Convert the given pallet `P` into its name as configured in the runtime.
	fn name<P: 'static>() -> Option<&'static str>;
}

/// The function and pallet name of the Call.
#[derive(Clone, Eq, PartialEq, Default, RuntimeDebug)]
pub struct CallMetadata {
	/// Name of the function.
	pub function_name: &'static str,
	/// Name of the pallet to which the function belongs.
	pub pallet_name: &'static str,
}

/// Gets the function name of the Call.
pub trait GetCallName {
	/// Return all function names.
	fn get_call_names() -> &'static [&'static str];
	/// Return the function name of the Call.
	fn get_call_name(&self) -> &'static str;
}

/// Gets the metadata for the Call - function name and pallet name.
pub trait GetCallMetadata {
	/// Return all module names.
	fn get_module_names() -> &'static [&'static str];
	/// Return all function names for the given `module`.
	fn get_call_names(module: &str) -> &'static [&'static str];
	/// Return a [`CallMetadata`], containing function and pallet name of the Call.
	fn get_call_metadata(&self) -> CallMetadata;
}

/// The block finalization trait.
///
/// Implementing this lets you express what should happen for your pallet when the block is ending.
#[impl_for_tuples(30)]
pub trait OnFinalize<BlockNumber> {
	/// The block is being finalized. Implement to have something happen.
	///
	/// NOTE: This function is called AFTER ALL extrinsics in a block are applied,
	/// including inherent extrinsics.
	fn on_finalize(_n: BlockNumber) {}
}

/// The block's on idle trait.
///
/// Implementing this lets you express what should happen for your pallet before
/// block finalization (see `on_finalize` hook) in case any remaining weight is left.
pub trait OnIdle<BlockNumber> {
	/// The block is being finalized.
	/// Implement to have something happen in case there is leftover weight.
	/// Check the passed `remaining_weight` to make sure it is high enough to allow for
	/// your pallet's extra computation.
	///
	/// NOTE: This function is called AFTER ALL extrinsics - including inherent extrinsics -
	/// in a block are applied but before `on_finalize` is executed.
	fn on_idle(
		_n: BlockNumber,
		_remaining_weight: crate::weights::Weight
	) -> crate::weights::Weight {
		0
	}
}

#[impl_for_tuples(30)]
impl<BlockNumber: Clone> OnIdle<BlockNumber> for Tuple {
	fn on_idle(n: BlockNumber,  remaining_weight: crate::weights::Weight) -> crate::weights::Weight {
		let mut weight = 0;
		for_tuples!( #(
			let adjusted_remaining_weight = remaining_weight.saturating_sub(weight);
			weight = weight.saturating_add(Tuple::on_idle(n.clone(),  adjusted_remaining_weight));
		)* );
		weight
	}
}

/// The block initialization trait.
///
/// Implementing this lets you express what should happen for your pallet when the block is
/// beginning (right before the first extrinsic is executed).
pub trait OnInitialize<BlockNumber> {
	/// The block is being initialized. Implement to have something happen.
	///
	/// Return the non-negotiable weight consumed in the block.
	///
	/// NOTE: This function is called BEFORE ANY extrinsic in a block is applied,
	/// including inherent extrinsics. Hence for instance, if you runtime includes
	/// `pallet_timestamp`, the `timestamp` is not yet up to date at this point.
	fn on_initialize(_n: BlockNumber) -> crate::weights::Weight { 0 }
}

#[impl_for_tuples(30)]
impl<BlockNumber: Clone> OnInitialize<BlockNumber> for Tuple {
	fn on_initialize(n: BlockNumber) -> crate::weights::Weight {
		let mut weight = 0;
		for_tuples!( #( weight = weight.saturating_add(Tuple::on_initialize(n.clone())); )* );
		weight
	}
}

/// A trait that will be called at genesis.
///
/// Implementing this trait for a pallet let's you express operations that should
/// happen at genesis. It will be called in an externalities provided environment and
/// will see the genesis state after all pallets have written their genesis state.
#[impl_for_tuples(30)]
pub trait OnGenesis {
	/// Something that should happen at genesis.
	fn on_genesis() {}
}

/// Prefix to be used (optionally) for implementing [`OnRuntimeUpgradeHelpersExt::storage_key`].
#[cfg(feature = "try-runtime")]
pub const ON_RUNTIME_UPGRADE_PREFIX: &[u8] = b"__ON_RUNTIME_UPGRADE__";
=======
mod members;
pub use members::{
	Contains, ContainsLengthBound, SortedMembers, InitializeMembers, ChangeMembers, All, IsInVec,
	AsContains,
};
>>>>>>> 37e97cfec065fe4acc9712b4dd9a79ec1936fa7d

mod validation;
pub use validation::{
	ValidatorSet, ValidatorSetWithIdentification, OneSessionHandler, FindAuthor, VerifySeal,
	EstimateNextNewSession, EstimateNextSessionRotation, KeyOwnerProofSystem, ValidatorRegistration,
	Lateness,
};

mod filter;
pub use filter::{
	Filter, FilterStack, FilterStackGuard, ClearFilterGuard, InstanceFilter, IntegrityTest,
};

mod misc;
pub use misc::{
	Len, Get, GetDefault, HandleLifetime, TryDrop, Time, UnixTime, IsType, IsSubType, ExecuteBlock,
	SameOrOther, OnNewAccount, OnKilledAccount, OffchainWorker, GetBacking, Backing, ExtrinsicCall,
	EnsureInherentsAreFirst,
};

mod stored_map;
pub use stored_map::{StoredMap, StorageMapShim};
mod randomness;
pub use randomness::Randomness;

mod metadata;
pub use metadata::{
	CallMetadata, GetCallMetadata, GetCallName, PalletInfo, PalletVersion, GetPalletVersion,
	PALLET_VERSION_STORAGE_KEY_POSTFIX, PalletInfoAccess,
};

mod hooks;
pub use hooks::{Hooks, OnGenesis, OnInitialize, OnFinalize, OnIdle, OnRuntimeUpgrade, OnTimestampSet};
#[cfg(feature = "try-runtime")]
pub use hooks::{OnRuntimeUpgradeHelpersExt, ON_RUNTIME_UPGRADE_PREFIX};
#[cfg(feature = "std")]
pub use hooks::GenesisBuild;

pub mod schedule;
mod storage;
pub use storage::{Instance, StorageInstance};

mod dispatch;
pub use dispatch::{EnsureOrigin, OriginTrait, UnfilteredDispatchable};

mod voting;
pub use voting::{CurrencyToVote, SaturatingCurrencyToVote, U128CurrencyToVote};
