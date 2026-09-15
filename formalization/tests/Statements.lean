import QiushiMatmul

open Matrix BigOperators

namespace QiushiMatmul

example : RankAtLeast 21 := rank_ge_21

example : QuotientRankAtLeast (spanCodes [1]) 19 := line_rank1_ge19

example : RankAtLeast 21 ∧ TensorEntryRankAtMost 23 := rank_between_21_and_23

-- State the operational target without a finite-certificate hypothesis.
example (r : Nat)
    (A B C : Fin r -> Matrix (Fin 3) (Fin 3) (ZMod 2))
    (h : ∀ X Y : Matrix (Fin 3) (Fin 3) (ZMod 2),
      X * Y = ∑ t : Fin r,
        ((∑ a : Fin 3 × Fin 3, A t a.1 a.2 * X a.1 a.2) *
          (∑ b : Fin 3 × Fin 3, B t b.1 b.2 * Y b.1 b.2)) • C t) :
    21 ≤ r :=
  bilinear_mul_requires_21 r A B C h

#print axioms rank_ge_21
#print axioms provedFinitePremises
#print axioms rank_between_21_and_23
#print axioms bilinear_mul_requires_21
#print axioms rank23_mul_eq
#print axioms E11SubspaceCount.e11_all_subspace_count
#print axioms E11SubspaceCount.e11_occupation_index_complete
#print axioms TailPadded.zero_A_excess_saturation
#print axioms TailPadded.length22_A_profiles_or_zero_excess_length21

end QiushiMatmul
