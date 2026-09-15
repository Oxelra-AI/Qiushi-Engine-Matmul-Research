import QiushiCompositionCheck
import QiushiMonoOrbit414From262
import QiushiBranch415Extraction
import QiushiBranch416Extraction
import QiushiPlane484GenFinal

/-! The normalized affine-hyperplane bounds and plane 484 bound are proved
here, rather than retained as assumptions of the final structural argument.
The remaining line and seven plane bounds are still explicit hypotheses. -/

namespace QiushiMatmul

theorem affineHyperplane0_rank_ge_17 : QuotientRankAtLeast affineHyperplane0 17 :=
  orbit414_lb17_mono

theorem affineHyperplane1_rank_ge_17 : QuotientRankAtLeast affineHyperplane1 17 :=
  step113_orbit415_lb17

theorem affineHyperplane2_rank_ge_17 : QuotientRankAtLeast affineHyperplane2 17 :=
  step113_orbit416_lb17

theorem plane484_rank_ge_19 : QuotientRankAtLeast plane484 19 :=
  plane484Gen_lb19

theorem rank_ge_21_of_remaining_finite_bounds
    (hLine1 : QuotientRankAtLeast lineRank1 19)
    (h485 : QuotientRankAtLeast plane485 19)
    (h486 : QuotientRankAtLeast plane486 19)
    (h487 : QuotientRankAtLeast plane487 19)
    (h488 : QuotientRankAtLeast plane488 19)
    (h489 : QuotientRankAtLeast plane489 19)
    (h490 : QuotientRankAtLeast plane490 19)
    (h491 : QuotientRankAtLeast plane491 19) : RankAtLeast 21 :=
  rank_ge_21_of_orbit_theorems hLine1 plane484_rank_ge_19 h485 h486 h487 h488 h489 h490 h491
    affineHyperplane0_rank_ge_17 affineHyperplane1_rank_ge_17 affineHyperplane2_rank_ge_17

end QiushiMatmul
