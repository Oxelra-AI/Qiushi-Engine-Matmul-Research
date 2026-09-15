import QiushiFrozenRankCoverMixed

open QiushiMatmul BigOperators

example {W : Submodule F2 Mat3} {n r : Nat}
    (U : Fin n → Submodule F2 Mat3) (lower : Fin n → Nat)
    (hWU : ∀ i, W ≤ U i) (hRank : ∀ i, QuotientRankAtLeast (U i) (lower i))
    (hCover : ∀ M : Mat3, ∃ i, M ∈ U i)
    (D : QuotientTensorDecomp W r) (hmr : ∀ i, lower i ≤ r) :
    r ≤ ∑ i : Fin n, (r - lower i) :=
  decomp_length_le_sum_cover_capacities U lower hWU hRank hCover D hmr

example {n bound : Nat} (basis : List Nat) (sources : Fin n → List Nat)
    (lower : Fin n → Nat)
    (hRank : ∀ i, QuotientRankAtLeast (spanCodes (sources i)) (lower i))
    (hLe : ∀ i g, g ∈ basis → spanContainsCode (sources i) g = true)
    (hCover : ∀ c : Fin 512, ∃ i, spanContainsCode (sources i) c.val = true)
    (hCapacity : ∀ r, r < bound → (∀ i, lower i ≤ r) →
      (∑ i : Fin n, (r - lower i)) < r) :
    QuotientRankAtLeast (spanCodes basis) bound :=
  quotientRankAtLeast_of_mixed_code_cover basis sources lower hRank hLe hCover hCapacity

/-- info: 'QiushiMatmul.decomp_length_le_sum_cover_capacities' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decomp_length_le_sum_cover_capacities

/-- info: 'QiushiMatmul.quotientRankAtLeast_of_mixed_code_cover' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quotientRankAtLeast_of_mixed_code_cover
