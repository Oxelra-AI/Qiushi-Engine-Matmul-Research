import QiushiFrozenRankCover

open QiushiMatmul

example {W : Submodule F2 Mat3} {n m r : Nat}
    (U : Fin n → Submodule F2 Mat3) (hWU : ∀ i, W ≤ U i)
    (hRank : ∀ i, QuotientRankAtLeast (U i) m)
    (hCover : ∀ M : Mat3, ∃ i, M ∈ U i)
    (D : QuotientTensorDecomp W r) (hmr : m ≤ r) :
    r ≤ n * (r - m) :=
  decomp_length_le_cover_capacity U hWU hRank hCover D hmr

example {W : Submodule F2 Mat3} (U : Fin 7 → Submodule F2 Mat3)
    (hWU : ∀ i, W ≤ U i) (hRank : ∀ i, QuotientRankAtLeast (U i) 9)
    (hCover : ∀ M : Mat3, ∃ i, M ∈ U i) : QuotientRankAtLeast W 11 :=
  quotientRankAtLeast_eleven_of_seven_cover U hWU hRank hCover

example (basis : List Nat) (sources : Fin 7 → List Nat)
    (hRank : ∀ i, QuotientRankAtLeast (spanCodes (sources i)) 9)
    (hLe : ∀ i g, g ∈ basis → spanContainsCode (sources i) g = true)
    (hCover : ∀ c : Fin 512, ∃ i, spanContainsCode (sources i) c.val = true) :
    QuotientRankAtLeast (spanCodes basis) 11 :=
  quotientRankAtLeast_eleven_of_seven_code_cover basis sources hRank hLe hCover

/-- info: 'QiushiMatmul.decomp_length_le_cover_capacity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms decomp_length_le_cover_capacity

/-- info: 'QiushiMatmul.quotientRankAtLeast_eleven_of_seven_cover' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quotientRankAtLeast_eleven_of_seven_cover

/-- info: 'QiushiMatmul.quotientRankAtLeast_eleven_of_seven_code_cover' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms quotientRankAtLeast_eleven_of_seven_code_cover
