import QiushiFinitePremisesReducer
import QiushiRank21Root

/-!
# Composition check: reducer ∘ root

Verifies that the corrected finite hypotheses chain through
FinitePremises_of_orbit_theorems → rank_ge_21_of_premises → RankAtLeast 21.
The rank-one line bound is now a direct input; `plane479@19` is not a hypothesis.
-/

namespace QiushiMatmul

theorem rank_ge_21_of_orbit_theorems
    (hLine1 : QuotientRankAtLeast lineRank1 19)
    (h484  : QuotientRankAtLeast plane484 19)
    (h485  : QuotientRankAtLeast plane485 19)
    (h486  : QuotientRankAtLeast plane486 19)
    (h487  : QuotientRankAtLeast plane487 19)
    (h488  : QuotientRankAtLeast plane488 19)
    (h489  : QuotientRankAtLeast plane489 19)
    (h490  : QuotientRankAtLeast plane490 19)
    (h491  : QuotientRankAtLeast plane491 19)
    (h414  : QuotientRankAtLeast affineHyperplane0 17)
    (h415  : QuotientRankAtLeast affineHyperplane1 17)
    (h416  : QuotientRankAtLeast affineHyperplane2 17) :
    RankAtLeast 21 :=
  rank_ge_21_of_premises
    (FinitePremises_of_orbit_theorems hLine1 h484 h485 h486 h487 h488 h489 h490 h491 h414 h415 h416)

end QiushiMatmul
