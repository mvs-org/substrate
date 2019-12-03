// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Runtime Api to help discover authorities.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Codec};
use rstd::vec::Vec;

pub mod sr25519 {
	mod app_sr25519 {
		use app_crypto::{app_crypto, key_types::AUTHORITY_DISCOVERY, sr25519};
		app_crypto!(sr25519, AUTHORITY_DISCOVERY);
	}

	/// An authority_discovery authority keypair using S/R 25519 as its crypto.
	#[cfg(feature = "std")]
	pub type AuthorityPair = app_sr25519::Pair;

	/// An authority_discovery authority signature using S/R 25519 as its crypto.
	pub type AuthoritySignature = app_sr25519::Signature;

	/// An authority_discovery authority identifier using S/R 25519 as its crypto.
	pub type AuthorityId = app_sr25519::Public;
}

pub mod ed25519 {
	mod app_ed25519 {
		use app_crypto::{app_crypto, key_types::AUTHORITY_DISCOVERY, ed25519};
		app_crypto!(ed25519, AUTHORITY_DISCOVERY);
	}

	/// An authority_discovery authority keypair using Ed25519 as its crypto.
	#[cfg(feature = "std")]
	pub type AuthorityPair = app_ed25519::Pair;

	/// An authority_discovery authority signature using Ed25519 as its crypto.
	pub type AuthoritySignature = app_ed25519::Signature;

	/// An authority_discovery authority identifier using Ed25519 as its crypto.
	pub type AuthorityId = app_ed25519::Public;
}

sp_api::decl_runtime_apis! {
	/// The authority discovery api.
	///
	/// This api is used by the `core/authority-discovery` module to retrieve identifiers
	/// of the current authority set.
	pub trait AuthorityDiscoveryApi<AuthorityId: Codec> {
		/// Retrieve authority identifiers of the current authority set.
		fn authorities() -> Vec<AuthorityId>;
	}
}
