// Copyright 2018 Commonwealth Labs Inc.
// This file is part of Edgeware.

// Edgeware is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Edgeware is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Edgeware.  If not, see <http://www.gnu.org/licenses/>.

//! Runtime module for cross-chain bridge targetting Ethereum.
use rstd::prelude::*;
use rstd::result;

use substrate_primitives::u32_trait::Value as U32;
use primitives::traits::{Hash, EnsureOrigin, MaybeSerializeDebug, OnFinalise};
use srml_support::dispatch::{Result, Dispatchable, Parameter};
use srml_support::{StorageValue, StorageMap};
use system::{self, ensure_signed};

/// Simple index type for proposal counting.
pub type ProposalIndex = u32;

pub trait Trait: CouncilTrait + MaybeSerializeDebug {
    /// The outer origin type.
    type Origin: From<Origin>;

    /// The outer call dispatch type.
    type Proposal: Parameter + Dispatchable<Origin=<Self as Trait>::Origin> + MaybeSerializeDebug;

    /// The outer event type.
    type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

/// Origin for the bridge module.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Origin {
    /// It has been condoned by a given number of bridge authorities.
    Authorities(u32),
}

/// Event for this module.
decl_event!(
    pub enum Event<T> where <T as system::Trait>::Hash, <T as system::Trait>::AccountId {
        /// A deposit (given hash) has been proposed (by given account) with a target account,
        /// a target amount, and an indicator for a deposit proposal or a withdraw proposal.
        DepositProposed(AccountId, ProposalIndex, Hash, AccountId, u64),
        /// A withdrawal (given hash) has been proposed (by given account) with a target account,
        /// a target amount, and an indicator for a deposit proposal or a withdraw proposal.
        WithdrawalProposed(AccountId, ProposalIndex, Hash, AccountId, u64),
        /// A motion (given hash) has been voted on by given bridge authority, leaving
        /// a tally (yes vote stake and no vote stake given as u64s respectively).
        Voted(AccountId, Hash, bool, u64, u64),
        /// A motion was approved by the required threshold.
        Approved(Hash),
        /// A motion was not approved by the required threshold.
        Disapproved(Hash),
        /// A motion was executed; `bool` is true if returned without error.
        Executed(Hash, bool),
    }
);

decl_storage! {
    trait Store for Module<T: Trait> as Bridge {
        /// The current set of validators.
        pub Validators get(validators) config(): Vec<T::AccountId>;
        /// The stake of each validator
        pub ValidatorStake get(validator) map T::AccountId => T::Balance;
        /// The total stake of the current validator set at a given block.
        pub TotalStake get(block_number): Option(T::Balance);
        /// The (hashes of) the active proposals.
        pub Proposals get(proposals): Vec<T::Hash>;
        /// Actual proposal for a given hash, if it's current.
        pub ProposalOf get(proposal_of): map T::Hash => Option< <T as Trait>::Proposal >;
        /// Votes for a given proposal: (yes_voters, no_voters).
        pub Voting get(voting): map T::Hash => Option<(ProposalIndex, Vec<T::AccountId>, Vec<T::AccountId>)>;
        /// Proposals so far.
        pub ProposalCount get(proposal_count): u32;
    }
};

impl<T: Trait> Module<T> {

    /// Deposit one of this module's events.
    fn deposit_event(event: Event<T>) {
        <system::Module<T>>::deposit_event(<T as Trait>::Event::from(event).into());
    }

    /// The number of validators currently.
    pub fn validator_count() -> u32 {
        <Validators<T>>::get().len() as u32 // TODO: can probably optimised
    }

    /// Set the current set of validators.
    ///
    /// Called by `staking::new_era()` only. This allows the bridge to know
    /// after each new session who is in the current set of validators.
    pub fn set_validators(new: &[T::AccountId], stake: &[T::Balance]) {
        <Validators<T>>::put(&new.to_vec());            // TODO: optimise.
        // Iterate over validators and add stake in order
        // TODO: Make efficient
    }
};
