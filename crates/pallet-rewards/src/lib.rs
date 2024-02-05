// Copyright (C) 2021 Subspace Labs, Inc.
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

//! Pallet for issuing rewards to block producers.

#![cfg_attr(not(feature = "std"), no_std)]
#![forbid(unsafe_code)]
#![warn(rust_2018_idioms, missing_debug_implementations)]

mod default_weights;

use frame_support::pallet_prelude::*;
use frame_support::traits::Currency;
use frame_system::pallet_prelude::*;
pub use pallet::*;
use subspace_runtime_primitives::{FindBlockRewardAddress, FindVotingRewardAddresses};

pub trait WeightInfo {
    fn on_initialize() -> Weight;
}

/// Hooks to notify when there are any rewards for specific account.
pub trait OnReward<AccountId, Balance> {
    fn on_reward(account: AccountId, reward: Balance);
}

impl<AccountId, Balance> OnReward<AccountId, Balance> for () {
    fn on_reward(_account: AccountId, _reward: Balance) {}
}

#[frame_support::pallet]
mod pallet {
    use super::{OnReward, WeightInfo};
    use frame_support::pallet_prelude::*;
    use frame_support::traits::Currency;
    use frame_system::pallet_prelude::*;
    use subspace_runtime_primitives::{FindBlockRewardAddress, FindVotingRewardAddresses};

    type BalanceOf<T> =
        <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

    /// Pallet rewards for issuing rewards to block producers.
    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// `pallet-rewards` events
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        type Currency: Currency<Self::AccountId>;

        /// Fixed reward for block producer.
        #[pallet::constant]
        type BlockReward: Get<BalanceOf<Self>>;

        /// Fixed reward for voter.
        #[pallet::constant]
        type VoteReward: Get<BalanceOf<Self>>;

        /// Number of blocks over which to compute average blockspace usage.
        #[pallet::constant]
        type AvgBlockspaceUsageNumBlocks: Get<u32>;

        type FindBlockRewardAddress: FindBlockRewardAddress<Self::AccountId>;

        type FindVotingRewardAddresses: FindVotingRewardAddresses<Self::AccountId>;

        type WeightInfo: WeightInfo;

        type OnReward: OnReward<Self::AccountId, BalanceOf<Self>>;
    }

    /// Utilization of blockspace (in bytes) by the normal extrinsics used to adjust issuance
    #[pallet::storage]
    pub(super) type AvgBlockspaceUsage<T> = StorageValue<_, u32, ValueQuery>;

    /// `pallet-rewards` events
    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Issued reward for the block author.
        BlockReward {
            block_author: T::AccountId,
            reward: BalanceOf<T>,
        },
        /// Issued reward for the voter.
        VoteReward {
            voter: T::AccountId,
            reward: BalanceOf<T>,
        },
    }

    #[pallet::hooks]
    impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
        fn on_initialize(block_number: BlockNumberFor<T>) -> Weight {
            Self::do_initialize(block_number);
            T::WeightInfo::on_initialize()
        }

        fn on_finalize(now: BlockNumberFor<T>) {
            Self::do_finalize(now);
        }
    }
}

impl<T: Config> Pallet<T> {
    fn do_initialize(_block_number: BlockNumberFor<T>) {
        // Block author may equivocate, in which case they'll not be present here
        if let Some(block_author) = T::FindBlockRewardAddress::find_block_reward_address() {
            let reward = T::BlockReward::get();
            let _imbalance = T::Currency::deposit_creating(&block_author, reward);
            T::OnReward::on_reward(block_author.clone(), reward);

            Self::deposit_event(Event::BlockReward {
                block_author,
                reward,
            });
        }
    }

    fn do_finalize(_block_number: BlockNumberFor<T>) {
        let used_blockspace = frame_system::Pallet::<T>::all_extrinsics_len();
        let avg_blockspace_usage = AvgBlockspaceUsage::<T>::get();
        let avg_blockspace_usage_num_blocks = T::AvgBlockspaceUsageNumBlocks::get();

        let avg_blockspace_usage = if frame_system::Pallet::<T>::block_number()
            <= avg_blockspace_usage_num_blocks.into()
        {
            (avg_blockspace_usage + used_blockspace) / 2
        } else {
            // Multiplier is `a / b` stored as `(a, b)`
            let multiplier = (2, u64::from(avg_blockspace_usage_num_blocks) + 1);

            // Equivalent to `multiplier * used_blockspace + (1 - multiplier) * avg_blockspace_usage`
            // using integer math
            let a = multiplier.0 * u64::from(used_blockspace);
            let b = (multiplier.1 - multiplier.0) * u64::from(avg_blockspace_usage);

            u32::try_from((a + b) / multiplier.1).expect(
                "Average of blockspace usage can't overflow if individual components do not \
                overflow; qed",
            )
        };

        AvgBlockspaceUsage::<T>::put(avg_blockspace_usage);

        let reward = T::VoteReward::get();

        for voter in T::FindVotingRewardAddresses::find_voting_reward_addresses() {
            let _imbalance = T::Currency::deposit_creating(&voter, reward);
            T::OnReward::on_reward(voter.clone(), reward);

            Self::deposit_event(Event::VoteReward { voter, reward });
        }
    }
}
