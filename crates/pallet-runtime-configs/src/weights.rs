
//! Autogenerated weights for pallet_runtime_configs
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2023-09-26, STEPS: `50`, REPEAT: `20`, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! WORST CASE MAP SIZE: `1000000`
//! HOSTNAME: `nazar-pc`, CPU: `13th Gen Intel(R) Core(TM) i9-13900K`
//! EXECUTION: , WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// target/release/subspace-node
// benchmark
// pallet
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_runtime_configs
// --extrinsic=*
// --heap-pages=4096
// --output=crates/pallet-runtime-configs/src/weights.rs
// --template=frame-weight-template.hbs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use core::marker::PhantomData;

/// Weight functions needed for pallet_runtime_configs.
pub trait WeightInfo {
	fn set_enable_domains() -> Weight;
	fn set_enable_dynamic_cost_of_storage() -> Weight;
	fn set_enable_balance_transfers() -> Weight;
	fn set_enable_non_root_calls() -> Weight;
}

/// Weights for pallet_runtime_configs using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	/// Storage: `RuntimeConfigs::EnableBalanceTransfers` (r:0 w:1)
	/// Proof: `RuntimeConfigs::EnableBalanceTransfers` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	fn set_enable_domains() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_640_000 picoseconds.
		Weight::from_parts(5_782_000, 0)
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: `RuntimeConfigs::EnableDynamicCostOfStorage` (r:0 w:1)
	/// Proof: `RuntimeConfigs::EnableDynamicCostOfStorage` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	fn set_enable_dynamic_cost_of_storage() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_726_000 picoseconds.
		Weight::from_parts(5_890_000, 0)
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: `RuntimeConfigs::EnableBalanceTransfers` (r:0 w:1)
	/// Proof: `RuntimeConfigs::EnableBalanceTransfers` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	fn set_enable_balance_transfers() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_726_000 picoseconds.
		Weight::from_parts(5_890_000, 0)
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
	/// Storage: `RuntimeConfigs::EnableNonRootCalls` (r:0 w:1)
	/// Proof: `RuntimeConfigs::EnableNonRootCalls` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	fn set_enable_non_root_calls() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_726_000 picoseconds.
		Weight::from_parts(5_890_000, 0)
			.saturating_add(T::DbWeight::get().writes(1_u64))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	/// Storage: `RuntimeConfigs::EnableBalanceTransfers` (r:0 w:1)
	/// Proof: `RuntimeConfigs::EnableBalanceTransfers` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	fn set_enable_domains() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_640_000 picoseconds.
		Weight::from_parts(5_782_000, 0)
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: `RuntimeConfigs::EnableDynamicCostOfStorage` (r:0 w:1)
	/// Proof: `RuntimeConfigs::EnableDynamicCostOfStorage` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	fn set_enable_dynamic_cost_of_storage() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_726_000 picoseconds.
		Weight::from_parts(5_890_000, 0)
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: `RuntimeConfigs::EnableBalanceTransfers` (r:0 w:1)
	/// Proof: `RuntimeConfigs::EnableBalanceTransfers` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	fn set_enable_balance_transfers() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_726_000 picoseconds.
		Weight::from_parts(5_890_000, 0)
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
	/// Storage: `RuntimeConfigs::EnableNonRootCalls` (r:0 w:1)
	/// Proof: `RuntimeConfigs::EnableNonRootCalls` (`max_values`: Some(1), `max_size`: Some(1), added: 496, mode: `MaxEncodedLen`)
	fn set_enable_non_root_calls() -> Weight {
		// Proof Size summary in bytes:
		//  Measured:  `0`
		//  Estimated: `0`
		// Minimum execution time: 5_726_000 picoseconds.
		Weight::from_parts(5_890_000, 0)
			.saturating_add(RocksDbWeight::get().writes(1_u64))
	}
}
