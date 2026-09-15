import QiushiRemainingPremises
import QiushiLineCoverageFinal
import QiushiPlane480GenFinal
import QiushiPlane481GenFinal
import QiushiPlane482GenFinal
import QiushiPlane483GenFinal
import QiushiPlane485GenFinal
import QiushiPlane486GenFinal
import QiushiPlane487GenFinal
import QiushiPlane488GenFinal
import QiushiPlane489GenFinal
import QiushiPlane490GenFinal
import QiushiPlane491GenFinal
import QiushiRank23UpperBound
import QiushiBilinearSemantics

namespace QiushiMatmul

theorem line_rank1_ge19 : QuotientRankAtLeast lineRank1 19 :=
  lineRank1_lb19_conditional plane480Gen_lb18 plane481Gen_lb18
    plane482Gen_lb18 plane483Gen_lb18

def provedFinitePremises : FinitePremises :=
  FinitePremises_of_orbit_theorems line_rank1_ge19
    plane484_rank_ge_19 plane485Gen_lb19 plane486Gen_lb19 plane487Gen_lb19
    plane488Gen_lb19 plane489Gen_lb19 plane490Gen_lb19 plane491Gen_lb19
    affineHyperplane0_rank_ge_17 affineHyperplane1_rank_ge_17
    affineHyperplane2_rank_ge_17

theorem rank_ge_21 : RankAtLeast 21 :=
  rank_ge_21_of_premises provedFinitePremises

theorem rank_between_21_and_23 : RankAtLeast 21 ∧ TensorEntryRankAtMost 23 :=
  rank_interval_21_23 provedFinitePremises

theorem bilinear_mul_requires_21 (r : Nat) (A B C : Fin r → Mat3)
    (h : ∀ X Y : Mat3, X * Y = bilinearAlgorithm A B C X Y) : 21 ≤ r :=
  (rankAtLeast_iff_bilinearAlgorithm 21).mp rank_ge_21 r A B C h

end QiushiMatmul
