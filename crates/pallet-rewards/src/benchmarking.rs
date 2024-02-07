//! Benchmarking for `pallet-rewards`.

use frame_benchmarking::v2::*;

#[benchmarks]
mod benchmarks {
    use crate::pallet::{ProposerSubsidyParams, VoterSubsidyParams};
    use crate::{Call, Config, IssuanceComponentParams, Pallet};
    use frame_system::RawOrigin;

    #[benchmark]
    fn update_issuance_params() {
        #[extrinsic_call]
        _(
            RawOrigin::Root,
            IssuanceComponentParams::default(),
            IssuanceComponentParams::default(),
        );

        assert!(ProposerSubsidyParams::<T>::get().is_some());
        assert!(VoterSubsidyParams::<T>::get().is_some());
    }
}
