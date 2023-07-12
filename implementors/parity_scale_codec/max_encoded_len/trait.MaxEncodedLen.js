(function() {var implementors = {
"evm_domain_runtime":[["impl MaxEncodedLen for <a class=\"enum\" href=\"evm_domain_runtime/enum.RuntimeSlashReason.html\" title=\"enum evm_domain_runtime::RuntimeSlashReason\">RuntimeSlashReason</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"evm_domain_runtime/enum.RuntimeFreezeReason.html\" title=\"enum evm_domain_runtime::RuntimeFreezeReason\">RuntimeFreezeReason</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"evm_domain_runtime/enum.OriginCaller.html\" title=\"enum evm_domain_runtime::OriginCaller\">OriginCaller</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"evm_domain_runtime/enum.RuntimeLockId.html\" title=\"enum evm_domain_runtime::RuntimeLockId\">RuntimeLockId</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"evm_domain_runtime/enum.RuntimeHoldReason.html\" title=\"enum evm_domain_runtime::RuntimeHoldReason\">RuntimeHoldReason</a>"]],
"evm_domain_test_runtime":[["impl MaxEncodedLen for <a class=\"enum\" href=\"evm_domain_test_runtime/enum.OriginCaller.html\" title=\"enum evm_domain_test_runtime::OriginCaller\">OriginCaller</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"evm_domain_test_runtime/enum.RuntimeLockId.html\" title=\"enum evm_domain_test_runtime::RuntimeLockId\">RuntimeLockId</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"evm_domain_test_runtime/enum.RuntimeSlashReason.html\" title=\"enum evm_domain_test_runtime::RuntimeSlashReason\">RuntimeSlashReason</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"evm_domain_test_runtime/enum.RuntimeHoldReason.html\" title=\"enum evm_domain_test_runtime::RuntimeHoldReason\">RuntimeHoldReason</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"evm_domain_test_runtime/enum.RuntimeFreezeReason.html\" title=\"enum evm_domain_test_runtime::RuntimeFreezeReason\">RuntimeFreezeReason</a>"]],
"orml_vesting":[["impl&lt;BlockNumber, Balance&gt; MaxEncodedLen for <a class=\"struct\" href=\"orml_vesting/struct.VestingSchedule.html\" title=\"struct orml_vesting::VestingSchedule\">VestingSchedule</a>&lt;BlockNumber, Balance&gt;<span class=\"where fmt-newline\">where\n    BlockNumber: MaxEncodedLen,\n    Balance: HasCompact + MaxEncodedLen + HasCompact,</span>"]],
"sp_consensus_subspace":[["impl MaxEncodedLen for <a class=\"struct\" href=\"sp_consensus_subspace/struct.GlobalRandomnesses.html\" title=\"struct sp_consensus_subspace::GlobalRandomnesses\">GlobalRandomnesses</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"sp_consensus_subspace/enum.ChainConstants.html\" title=\"enum sp_consensus_subspace::ChainConstants\">ChainConstants</a>"],["impl MaxEncodedLen for <a class=\"struct\" href=\"sp_consensus_subspace/struct.SolutionRanges.html\" title=\"struct sp_consensus_subspace::SolutionRanges\">SolutionRanges</a>"]],
"sp_domains":[["impl MaxEncodedLen for <a class=\"struct\" href=\"sp_domains/struct.DomainId.html\" title=\"struct sp_domains::DomainId\">DomainId</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"sp_domains/enum.DomainsFreezeIdentifier.html\" title=\"enum sp_domains::DomainsFreezeIdentifier\">DomainsFreezeIdentifier</a>"]],
"subspace_core_primitives":[["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_core_primitives/crypto/struct.Scalar.html\" title=\"struct subspace_core_primitives::crypto::Scalar\">Scalar</a>"],["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_core_primitives/struct.SegmentIndex.html\" title=\"struct subspace_core_primitives::SegmentIndex\">SegmentIndex</a>"],["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_core_primitives/struct.ArchivedHistorySegment.html\" title=\"struct subspace_core_primitives::ArchivedHistorySegment\">ArchivedHistorySegment</a>"],["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_core_primitives/struct.PieceOffset.html\" title=\"struct subspace_core_primitives::PieceOffset\">PieceOffset</a>"],["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_core_primitives/struct.PosProof.html\" title=\"struct subspace_core_primitives::PosProof\">PosProof</a>"],["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_core_primitives/crypto/kzg/struct.Witness.html\" title=\"struct subspace_core_primitives::crypto::kzg::Witness\">Witness</a>"],["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_core_primitives/crypto/kzg/struct.Commitment.html\" title=\"struct subspace_core_primitives::crypto::kzg::Commitment\">Commitment</a>"],["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_core_primitives/struct.PieceIndex.html\" title=\"struct subspace_core_primitives::PieceIndex\">PieceIndex</a>"],["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_core_primitives/struct.RecordWitness.html\" title=\"struct subspace_core_primitives::RecordWitness\">RecordWitness</a>"],["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_core_primitives/struct.RecordCommitment.html\" title=\"struct subspace_core_primitives::RecordCommitment\">RecordCommitment</a>"],["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_core_primitives/struct.SBucket.html\" title=\"struct subspace_core_primitives::SBucket\">SBucket</a>"],["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_core_primitives/struct.Randomness.html\" title=\"struct subspace_core_primitives::Randomness\">Randomness</a>"],["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_core_primitives/struct.HistorySize.html\" title=\"struct subspace_core_primitives::HistorySize\">HistorySize</a>"],["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_core_primitives/struct.PieceArray.html\" title=\"struct subspace_core_primitives::PieceArray\">PieceArray</a>"]],
"subspace_runtime":[["impl MaxEncodedLen for <a class=\"enum\" href=\"subspace_runtime/enum.RuntimeFreezeReason.html\" title=\"enum subspace_runtime::RuntimeFreezeReason\">RuntimeFreezeReason</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"subspace_runtime/enum.RuntimeSlashReason.html\" title=\"enum subspace_runtime::RuntimeSlashReason\">RuntimeSlashReason</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"subspace_runtime/enum.OriginCaller.html\" title=\"enum subspace_runtime::OriginCaller\">OriginCaller</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"subspace_runtime/enum.RuntimeLockId.html\" title=\"enum subspace_runtime::RuntimeLockId\">RuntimeLockId</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"subspace_runtime/enum.RuntimeHoldReason.html\" title=\"enum subspace_runtime::RuntimeHoldReason\">RuntimeHoldReason</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"subspace_runtime/enum.FreezeIdentifier.html\" title=\"enum subspace_runtime::FreezeIdentifier\">FreezeIdentifier</a>"]],
"subspace_test_runtime":[["impl MaxEncodedLen for <a class=\"enum\" href=\"subspace_test_runtime/enum.RuntimeHoldReason.html\" title=\"enum subspace_test_runtime::RuntimeHoldReason\">RuntimeHoldReason</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"subspace_test_runtime/enum.RuntimeFreezeReason.html\" title=\"enum subspace_test_runtime::RuntimeFreezeReason\">RuntimeFreezeReason</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"subspace_test_runtime/enum.RuntimeLockId.html\" title=\"enum subspace_test_runtime::RuntimeLockId\">RuntimeLockId</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"subspace_test_runtime/enum.OriginCaller.html\" title=\"enum subspace_test_runtime::OriginCaller\">OriginCaller</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"subspace_test_runtime/enum.FreezeIdentifier.html\" title=\"enum subspace_test_runtime::FreezeIdentifier\">FreezeIdentifier</a>"],["impl MaxEncodedLen for <a class=\"enum\" href=\"subspace_test_runtime/enum.RuntimeSlashReason.html\" title=\"enum subspace_test_runtime::RuntimeSlashReason\">RuntimeSlashReason</a>"]],
"subspace_verification":[["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_verification/struct.VerifySolutionParams.html\" title=\"struct subspace_verification::VerifySolutionParams\">VerifySolutionParams</a>"],["impl MaxEncodedLen for <a class=\"struct\" href=\"subspace_verification/struct.PieceCheckParams.html\" title=\"struct subspace_verification::PieceCheckParams\">PieceCheckParams</a>"]]
};if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()