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

//! Primitives for Messenger.

#![cfg_attr(not(feature = "std"), no_std)]

pub mod endpoint;
pub mod messages;

use crate::messages::BlockInfo;
use codec::{Decode, Encode};
use messages::{
    BlockMessagesWithStorageKey, ChainId, CrossDomainMessage, ExtractedStateRootsFromProof,
    MessageId,
};
use sp_domains::DomainId;
use sp_mmr_primitives::{EncodableOpaqueLeaf, Proof};
use sp_std::vec::Vec;

/// Trait to handle XDM rewards.
pub trait OnXDMRewards<Balance> {
    fn on_xdm_rewards(rewards: Balance);
}

impl<Balance> OnXDMRewards<Balance> for () {
    fn on_xdm_rewards(_: Balance) {}
}

/// Trait to verify MMR proofs
pub trait MmrProofVerifier<MmrHash, StateRoot> {
    /// Returns consensus state root if the given MMR proof is valid
    fn verify_proof_and_extract_consensus_state_root(
        leaf: EncodableOpaqueLeaf,
        proof: Proof<MmrHash>,
    ) -> Option<StateRoot>;
}

impl<MmrHash, StateRoot> MmrProofVerifier<MmrHash, StateRoot> for () {
    fn verify_proof_and_extract_consensus_state_root(
        _leaf: EncodableOpaqueLeaf,
        _proof: Proof<MmrHash>,
    ) -> Option<StateRoot> {
        None
    }
}

sp_api::decl_runtime_apis! {
    /// Api useful for relayers to fetch messages and submit transactions.
    pub trait RelayerApi< BlockNumber>
    where
        BlockNumber: Encode + Decode
    {
        /// Returns the the chain_id of the Runtime.
        fn chain_id() -> ChainId;

        /// Returns the confirmation depth to relay message.
        fn relay_confirmation_depth() -> BlockNumber;

        /// Returns all the outbox and inbox responses to deliver.
        /// Storage key is used to generate the storage proof for the message.
        fn block_messages() -> BlockMessagesWithStorageKey;

        /// Constructs an outbox message to the dst_chain as an unsigned extrinsic.
        fn outbox_message_unsigned(
            msg: CrossDomainMessage<BlockNumber, Block::Hash, Block::Hash>,
        ) -> Option<Block::Extrinsic>;

        /// Constructs an inbox response message to the dst_chain as an unsigned extrinsic.
        fn inbox_response_message_unsigned(
            msg: CrossDomainMessage<BlockNumber, Block::Hash, Block::Hash>,
        ) -> Option<Block::Extrinsic>;

        /// Returns true if the outbox message is ready to be relayed to dst_chain.
        fn should_relay_outbox_message(dst_chain_id: ChainId, msg_id: MessageId) -> bool;

        /// Returns true if the inbox message response is ready to be relayed to dst_chain.
        fn should_relay_inbox_message_response(dst_chain_id: ChainId, msg_id: MessageId) -> bool;
    }

    /// Api to provide XDM extraction from Runtime Calls.
    pub trait MessengerApi<BlockNumber> where BlockNumber: Encode + Decode{
        fn extract_xdm_proof_state_roots(
            extrinsic: Vec<u8>
        ) -> Option<ExtractedStateRootsFromProof<BlockNumber, Block::Hash, Block::Hash>>;

        fn is_domain_info_confirmed(
            domain_id: DomainId,
            domain_block_info: BlockInfo<BlockNumber, Block::Hash>,
            domain_state_root: Block::Hash,
        ) -> bool;
    }
}
