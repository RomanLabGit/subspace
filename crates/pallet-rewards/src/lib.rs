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
#![feature(try_blocks)]

mod default_weights;

use frame_support::pallet_prelude::*;
use frame_support::traits::Currency;
use frame_system::pallet_prelude::*;
use log::warn;
pub use pallet::*;
use sp_core::U256;
use sp_runtime::traits::{CheckedAdd, CheckedSub, Zero};
use sp_runtime::Saturating;
use subspace_runtime_primitives::{BlockNumber, FindBlockRewardAddress, FindVotingRewardAddresses};

type BalanceOf<T> =
    <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

pub trait WeightInfo {
    // TODO: We are doing non-trivial amount of work in block finalization, should we charge for it
    //  during initialization?
}

/// Hooks to notify when there are any rewards for specific account.
pub trait OnReward<AccountId, Balance> {
    fn on_reward(account: AccountId, reward: Balance);
}

impl<AccountId, Balance> OnReward<AccountId, Balance> for () {
    fn on_reward(_account: AccountId, _reward: Balance) {}
}

#[derive(Debug, Default, Copy, Clone, Encode, Decode, MaxEncodedLen, TypeInfo)]
struct IssuanceComponentParams<BlockNumber, Balance> {
    /// Maximum subsidy for initial issuance per block, total for all recipients
    initial_subsidy: Balance,
    /// Max SSC to be disbursed via this mechanism.
    ///
    /// It must be less than the remaining issuance at the time of initialization of this component.
    max_component_issuance: Balance,
    /// Block height at which constant reference subsidy issuance starts
    initial_subsidy_start_block: BlockNumber,
    /// Number of blocks for which `initial_subsidy` is issued before the exponential decay starts
    initial_subsidy_duration: BlockNumber,
}

#[frame_support::pallet]
mod pallet {
    use super::{BalanceOf, IssuanceComponentParams, OnReward, WeightInfo};
    use frame_support::pallet_prelude::*;
    use frame_support::traits::Currency;
    use frame_system::pallet_prelude::*;
    use subspace_runtime_primitives::{FindBlockRewardAddress, FindVotingRewardAddresses};

    /// Pallet rewards for issuing rewards to block producers.
    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config {
        /// `pallet-rewards` events
        type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

        type Currency: Currency<Self::AccountId>;

        /// Number of blocks over which to compute average blockspace usage
        #[pallet::constant]
        type AvgBlockspaceUsageNumBlocks: Get<u32>;

        /// Cost of one byte of blockspace
        #[pallet::constant]
        type TransactionByteFee: Get<BalanceOf<Self>>;

        /// Reward address of block producer
        type FindBlockRewardAddress: FindBlockRewardAddress<Self::AccountId>;

        /// Reward addresses of all receivers of voting rewards
        type FindVotingRewardAddresses: FindVotingRewardAddresses<Self::AccountId>;

        type WeightInfo: WeightInfo;

        type OnReward: OnReward<Self::AccountId, BalanceOf<Self>>;
    }

    #[pallet::genesis_config]
    #[derive(Debug)]
    pub struct GenesisConfig<T>
    where
        T: Config,
    {
        /// Tokens left to issue to farmers at any given time
        pub remaining_issuance: BalanceOf<T>,
    }

    impl<T> Default for GenesisConfig<T>
    where
        T: Config,
    {
        #[inline]
        fn default() -> Self {
            Self {
                remaining_issuance: Default::default(),
            }
        }
    }

    #[pallet::genesis_build]
    impl<T> BuildGenesisConfig for GenesisConfig<T>
    where
        T: Config,
    {
        fn build(&self) {
            RemainingIssuance::<T>::put(self.remaining_issuance);
        }
    }

    /// Utilization of blockspace (in bytes) by the normal extrinsics used to adjust issuance
    #[pallet::storage]
    pub(super) type AvgBlockspaceUsage<T> = StorageValue<_, u32, ValueQuery>;

    /// Tokens left to issue to farmers at any given time
    #[pallet::storage]
    pub(super) type RemainingIssuance<T> = StorageValue<_, BalanceOf<T>, ValueQuery>;

    /// Block proposer subsidy parameters
    #[pallet::storage]
    pub(super) type ProposerSubsidyParams<T> =
        StorageValue<_, IssuanceComponentParams<BlockNumberFor<T>, BalanceOf<T>>, OptionQuery>;

    /// Voter subsidy parameters
    #[pallet::storage]
    pub(super) type VoterSubsidyParams<T> =
        StorageValue<_, IssuanceComponentParams<BlockNumberFor<T>, BalanceOf<T>>, OptionQuery>;

    /// `pallet-rewards` events
    #[pallet::event]
    #[pallet::generate_deposit(pub(super) fn deposit_event)]
    pub enum Event<T: Config> {
        /// Issued reward for the block author
        BlockReward {
            block_author: T::AccountId,
            reward: BalanceOf<T>,
        },
        /// Issued reward for the voter
        VoteReward {
            voter: T::AccountId,
            reward: BalanceOf<T>,
        },
    }

    #[pallet::hooks]
    impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
        fn on_finalize(now: BlockNumberFor<T>) {
            Self::do_finalize(now);
        }
    }
}

impl<T: Config> Pallet<T> {
    fn do_finalize(block_number: BlockNumberFor<T>) {
        let used_blockspace = frame_system::Pallet::<T>::all_extrinsics_len();
        let old_avg_blockspace_usage = AvgBlockspaceUsage::<T>::get();
        let avg_blockspace_usage_num_blocks = T::AvgBlockspaceUsageNumBlocks::get();

        let new_avg_blockspace_usage = if frame_system::Pallet::<T>::block_number()
            <= avg_blockspace_usage_num_blocks.into()
        {
            (old_avg_blockspace_usage + used_blockspace) / 2
        } else {
            // Multiplier is `a / b` stored as `(a, b)`
            let multiplier = (2, u64::from(avg_blockspace_usage_num_blocks) + 1);

            // Equivalent to `multiplier * used_blockspace + (1 - multiplier) * avg_blockspace_usage`
            // using integer math
            let a = multiplier.0 * u64::from(used_blockspace);
            let b = (multiplier.1 - multiplier.0) * u64::from(old_avg_blockspace_usage);

            u32::try_from((a + b) / multiplier.1).expect(
                "Average of blockspace usage can't overflow if individual components do not \
                overflow; qed",
            )
        };

        AvgBlockspaceUsage::<T>::put(new_avg_blockspace_usage);

        let old_remaining_issuance = RemainingIssuance::<T>::get();
        let mut new_remaining_issuance = old_remaining_issuance;

        // Block author may equivocate, in which case they'll not be present here
        if let Some(block_author) = T::FindBlockRewardAddress::find_block_reward_address() {
            // Can't exceed remaining issuance
            let block_reward = Self::block_reward(block_number, new_avg_blockspace_usage)
                .min(new_remaining_issuance);
            new_remaining_issuance -= block_reward;

            if !block_reward.is_zero() {
                let _imbalance = T::Currency::deposit_creating(&block_author, block_reward);
                T::OnReward::on_reward(block_author.clone(), block_reward);

                Self::deposit_event(Event::BlockReward {
                    block_author,
                    reward: block_reward,
                });
            }
        }

        let voters = T::FindVotingRewardAddresses::find_voting_reward_addresses();
        if !voters.is_empty() {
            let vote_reward = Self::vote_reward(block_number);

            for voter in voters {
                // Can't exceed remaining issuance
                let reward = vote_reward.min(new_remaining_issuance);
                new_remaining_issuance -= reward;

                if !reward.is_zero() {
                    let _imbalance = T::Currency::deposit_creating(&voter, reward);
                    T::OnReward::on_reward(voter.clone(), reward);

                    Self::deposit_event(Event::VoteReward { voter, reward });
                }
            }
        }

        if old_remaining_issuance != new_remaining_issuance {
            RemainingIssuance::<T>::put(new_remaining_issuance);
        }
    }

    fn block_reward(block_height: BlockNumberFor<T>, avg_blockspace_usage: u32) -> BalanceOf<T> {
        let Some(proposer_subsidy_params) = ProposerSubsidyParams::<T>::get() else {
            return Zero::zero();
        };
        let reference_subsidy =
            Self::reference_subsidy_for_block(proposer_subsidy_params, block_height);
        let max_normal_block_length = *T::BlockLength::get().max.get(DispatchClass::Normal);
        let max_block_fee = BalanceOf::<T>::from(max_normal_block_length)
            .saturating_mul(T::TransactionByteFee::get());

        // Code below is the same as:
        // ```
        // b = 2000 / 1523 * reference_subsidy.min(max_block_fee)
        // blockspace_utilization = avg_blockspace_usage / max_normal_block_length
        // reference_subsidy - b * (1523 / 2000 - 3 / 4 * (1 - blockspace_utilization))
        // ```
        // But written with just integers.
        // Step 1 (inline `blockspace_utilization`):
        // ```
        // reference_subsidy - b * (1523 / 2000 - 3 / 4 * (1 - avg_blockspace_usage / max_normal_block_length))
        // ```
        // Step 2 (move `max_normal_block_length` out):
        // ```
        // reference_subsidy - b * (1523 / 2000 - 3 / 4 * (max_normal_block_length - avg_blockspace_usage) / max_normal_block_length)
        // ```
        // Step 3 (common denominator):
        // ```
        // reference_subsidy - b * (1523 * max_normal_block_length - 3 * 500 * (max_normal_block_length - avg_blockspace_usage)) / max_normal_block_length / 2000
        // ```
        // Step 4 (inline `b`):
        // ```
        // reference_subsidy - reference_subsidy.min(max_block_fee) * (1523 * max_normal_block_length - 3 * 500 * (max_normal_block_length - avg_blockspace_usage)) / max_normal_block_length / 1523
        // ```

        // Reward decrease based on chain utilization
        let reward_decrease = reference_subsidy.min(max_block_fee).saturating_mul(
            (Self::block_number_to_balance(1523_u32)
                * Self::block_number_to_balance(max_normal_block_length))
            .saturating_sub(
                Self::block_number_to_balance(3_u32 * 500)
                    * Self::block_number_to_balance(max_normal_block_length - avg_blockspace_usage),
            ),
        ) / Self::block_number_to_balance(max_normal_block_length)
            / 1523_u32.into();
        reference_subsidy.saturating_sub(reward_decrease)
    }

    fn vote_reward(block_height: BlockNumberFor<T>) -> BalanceOf<T> {
        let Some(voter_subsidy_params) = VoterSubsidyParams::<T>::get() else {
            return Zero::zero();
        };
        Self::reference_subsidy_for_block(voter_subsidy_params, block_height)
    }

    fn reference_subsidy_for_block(
        params: IssuanceComponentParams<BlockNumberFor<T>, BalanceOf<T>>,
        block_height: BlockNumberFor<T>,
    ) -> BalanceOf<T> {
        if block_height < params.initial_subsidy_start_block {
            return Zero::zero();
        }

        let decay_start_block = params
            .initial_subsidy_start_block
            .saturating_add(params.initial_subsidy_duration);
        let t = match block_height.checked_sub(&decay_start_block) {
            Some(t) => Self::block_number_to_balance(t),
            None => {
                return params.initial_subsidy;
            }
        };

        let total_initial_subsidy = Self::block_number_to_balance(params.initial_subsidy_duration)
            .saturating_mul(params.initial_subsidy);
        let maybe_max_decay_issuance = params
            .max_component_issuance
            .checked_sub(&total_initial_subsidy);
        let Some(max_decay_issuance) = maybe_max_decay_issuance else {
            warn!(
                "`max_decay_issuance` underflow when calculating reference subsidy, incorrect \
                issuance parameters"
            );

            return Zero::zero();
        };

        // Code below is the same as:
        // ```
        // k = params.initial_subsidy / max_decay_issuance
        // params.initial_subsidy*(1 - k*t + (k*t)^2/2 - (k*t)^3/6 + (k*t)^4/24 - (k*t)^5/120)
        // ```
        // But written with just integers.
        //
        // Step 1 (multiply everything by `initial_subsidy`):
        // ```
        // is = params.initial_subsidy
        // mdi = max_decay_issuance
        // is
        //   - is*is/mdi*t
        //   + is*(is/mdi*t)^2/2
        //   - is*(is/mdi*t)^3/6
        //   + is*(is/mdi*t)^4/24
        //   - is*(is/mdi*t)^5/120
        // ```
        // Step 2 (expand powers):
        // ```
        // is
        //   - is*is/mdi*t
        //   + is*is*is/mdi/mdi*t*t/2
        //   - is*is*is*is/mdi/mdi/mdi*t*t*t/6
        //   + is*is*is*is*is/mdi/mdi/mdi/mdi*t*t*t*t/24
        //   - is*is*is*is*is*is/mdi/mdi/mdi/mdi/mdi*t*t*t*t*t/120
        // ```
        // Step 3 (reorder to avoid integer overflow or zeroing):
        // ```
        // is
        //   - is*is*t/mdi
        //   + is*is*t/mdi*is*t/mdi/2
        //   - is*is*t/mdi*is*t/mdi*is*t/mdi/6
        //   + is*is*t/mdi*is*t/mdi*is*t/mdi*is*t/mdi/24
        //   - is*is*t/mdi*is*t/mdi*is*t/mdi*is*t/mdi*is*t/mdi/120
        // ```

        let is = params.initial_subsidy;
        let mdi = max_decay_issuance;

        let maybe_subsidy = try {
            is.checked_sub(&(is * is * t / mdi))?
                .checked_add(&(is * is * t / mdi * is * t / mdi / 2_u32.into()))?
                .checked_sub(&(is * is * t / mdi * is * t / mdi * is * t / mdi / 6_u32.into()))?
                .checked_add(
                    &(is * is * t / mdi * is * t / mdi * is * t / mdi * is * t
                        / mdi
                        / 24_u32.into()),
                )?
                .checked_sub(
                    &(is * is * t / mdi * is * t / mdi * is * t / mdi * is * t / mdi * is * t
                        / mdi
                        / 120_u32.into()),
                )?
        };

        match maybe_subsidy {
            Some(subsidy) => subsidy,
            None => {
                warn!(
                    "Underflow or overflow when calculating reference subsidy, incorrect \
                    issuance parameters"
                );

                Zero::zero()
            }
        }
    }

    fn block_number_to_balance<N>(n: N) -> BalanceOf<T>
    where
        N: Into<BlockNumberFor<T>>,
    {
        let n = Into::<BlockNumberFor<T>>::into(n);
        BalanceOf::<T>::from(
            BlockNumber::try_from(Into::<U256>::into(n))
                .expect("Block number fits into block number; qed"),
        )
    }
}
