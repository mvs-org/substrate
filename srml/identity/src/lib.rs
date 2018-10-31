// Copyright 2018 Commonwealth Labs, Inc.
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

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
#[macro_use]
extern crate serde_derive;

#[cfg(test)]
#[macro_use]
extern crate parity_codec_derive;

#[cfg_attr(test, macro_use)]
extern crate srml_support as runtime_support;

#[cfg_attr(not(feature = "std"), macro_use)]
extern crate sr_std as rstd;
extern crate sr_io as runtime_io;
extern crate parity_codec as codec;
extern crate sr_primitives as primitives;
extern crate srml_system as system;

#[cfg(test)]
#[macro_use]
extern crate hex_literal;

#[cfg(test)]
extern crate substrate_primitives;

#[cfg(test)]
extern crate srml_balances as balances;

use rstd::prelude::*;
use runtime_support::{StorageValue, StorageMap, Parameter};
use runtime_support::dispatch::Result;

/// An identity index.
pub type IdentityIndex = u32;

/// Determinator for whether a given account is able to transfer balance.
pub trait EnsureLinked<Hash> {
    /// Returns `Ok` iff the Identity has a link.
    /// Returns `Err(...)` with why not otherwise.
    fn ensure_linked(message_hash: &Hash) -> Result;
}

pub trait Trait: balances::Trait {
    /// An identity type
    type Identity: Parameter + Default + Copy;
    /// A function that returns true iff a given identity has linked its identity attestation proof.
    type EnsureLinked: EnsureLinked<Hash>;
    /// The overarching event type.
    type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}


// External identity should be a packed array of bytes representing the
// organization and the identity - { org, identity }
// Packed encoding - [length of "github" in bytes, "github" in bytes, "drewstone" in bytes]
pub type ExternalIdentity = [u8];
pub type SigHash = [u8; 32];

/// An event in this module.
decl_event!(
    pub enum Event<T> where <T as system::Trait>::Hash, <T as system::Trait>::AccountId {
        Published(Hash, IdentityIndex, AccountId)
        Linked(Hash, IdentityIndex, AccountId)
    }
);

decl_storage! {
    trait Store for Module<T: Trait> as IdentityLinks {
        /// The number of identities that have been added.
        pub IdentityCount get(identity_count) build(|_| 0 as IdentityIndex) : IdentityIndex;
        /// The identities.
        pub Identities get(identities): Vec<(IdentityIndex, T::IdentityLink, T::AccountId)>;
        /// Actual identity for a given hash, if it's current.
        pub IdentityOf get(identity_of): map T::Hash => Option< <T as Trait>::Proposal >;
        /// The number of linked identities that have been added.
        pub LinkedIdentityCount get(linked_identity_count): build(|_| 0 as IdentityIndex)
    }
}


decl_module! {
    pub struct Module<T: Trait> for enum Call where origin: T::Origin {
        fn deposit_event() = default;

        fn publish(origin, T::Origin, external_identity: ExternalIdentity, sig_hash: SigHash) -> Result {
            let _sender = ensure_signed(origin)?;
            <PublicIdentities<T>>::put()

        }
    }
}