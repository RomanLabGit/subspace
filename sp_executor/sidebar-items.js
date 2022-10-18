window.SIDEBAR_ITEMS = {"enum":[["ExecutionPhase","Execution phase along with an optional encoded call data."],["InvalidTransactionCode","Custom invalid validity code for the extrinsics in pallet-executor."],["ReadBundleElectionParamsError",""],["VerificationError","Error type of fraud proof verification on primary node."],["VrfProofError",""]],"fn":[["calculate_bundle_election_threshold","Returns the election threshold based on the stake weight proportion and slot probability."],["derive_bundle_election_solution","Returns the solution for the challenge of producing a bundle."],["is_election_solution_within_threshold",""],["make_local_randomness_transcript","Make a VRF transcript."],["make_local_randomness_transcript_data","Make a VRF transcript data."],["read_bundle_election_params","Returns the bundle election parameters read from the given storage proof."],["verify_vrf_proof","Verify the vrf proof generated in the bundle election."]],"mod":[["well_known_keys",""]],"struct":[["Bundle","Transaction bundle"],["BundleElectionParams","Parameters for the bundle election."],["BundleEquivocationProof","Represents a bundle equivocation proof. An equivocation happens when an executor produces more than one bundle on the same slot. The proof of equivocation are the given distinct bundle headers that were signed by the validator and which include the slot number."],["BundleHeader","Header of transaction bundle."],["ExecutionReceipt","Receipt of state execution."],["ExecutorKey","A type that implements `BoundToRuntimeAppPublic`, used for executor signing key."],["FraudProof","Fraud proof for the state computation."],["InvalidTransactionProof","Represents an invalid transaction proof."],["ProofOfElection",""],["SignedBundle","Signed version of [`Bundle`]."],["SignedExecutionReceipt","Signed version of [`ExecutionReceipt`] which will be gossiped over the executors network."]],"trait":[["ExecutorApi","API necessary for executor pallet."]],"type":[["DomainId","Unique identifier for each domain."],["ExecutorId","An executor authority identifier."],["ExecutorPair","An executor authority keypair. Necessarily equivalent to the schnorrkel public key used in the main executor module. If that ever changes, then this must, too."],["ExecutorSignature","An executor authority signature."],["OpaqueBundle","Bundle with opaque extrinsics."],["SignedOpaqueBundle","[`SignedBundle`] with opaque extrinsic."],["StakeWeight","Stake weight in the domain bundle election."]]};