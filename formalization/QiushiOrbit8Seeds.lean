import QiushiContractionSeed

/-!
# Concrete contraction seeds for the orbit-8 pilot

This file instantiates the contraction-seed theorem for the three linear
functionals used in the closed orbit-8 weighted-cover test:

* `272`: `M₁₁ + M₂₂`;
* `416`: `M₁₂ + M₂₁ + M₂₂`;
* `176`: `M₁₁ + M₁₂ + M₂₁`.

For code `272` the selected 6×6 contraction minor is the identity.  For codes
`416` and `176` it is an invertible Kronecker block, not the identity; we prove
invertibility by kernel-checking an explicit inverse minor.  No `native_decide`
is used.
-/

set_option maxHeartbeats 16000000
open BigOperators Finset Matrix
namespace QiushiMatmul

-- ============================================================================
-- The 6 coordinate pairs for the lower-right 2×2 block tensored by I₃
-- ============================================================================

/-- Coordinates `(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)` in the B/C slots. -/
def seed6 : Fin 6 → Coord9
  | ⟨0, _⟩ => ((1 : I3), (0 : I3))
  | ⟨1, _⟩ => ((1 : I3), (1 : I3))
  | ⟨2, _⟩ => ((1 : I3), (2 : I3))
  | ⟨3, _⟩ => ((2 : I3), (0 : I3))
  | ⟨4, _⟩ => ((2 : I3), (1 : I3))
  | ⟨5, _⟩ => ((2 : I3), (2 : I3))

/-- The 272 contraction minor is exactly `I₆`. -/
theorem seed_minor_272_left_inverse :
    (1 : Matrix (Fin 6) (Fin 6) F2) *
        contractionMinor (codeMat 272) seed6 seed6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The code-176 minor is a left inverse for the code-416 minor. -/
theorem seed_minor_416_left_inverse :
    contractionMinor (codeMat 176) seed6 seed6 *
        contractionMinor (codeMat 416) seed6 seed6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The code-416 minor is a left inverse for the code-176 minor. -/
theorem seed_minor_176_left_inverse :
    contractionMinor (codeMat 416) seed6 seed6 *
        contractionMinor (codeMat 176) seed6 seed6 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

-- ============================================================================
-- The three quotient-rank seed bounds
-- ============================================================================

/-- QuotientRankAtLeast for the kernel of `f(M)=M₁₁+M₂₂`. -/
theorem seed_ker_272 : QuotientRankAtLeast (kerEvalFunc (codeMat 272)) 6 :=
  contraction_seed_ker_invertible_minor (codeMat 272) 6 seed6 seed6
    (1 : Matrix (Fin 6) (Fin 6) F2) seed_minor_272_left_inverse

/-- QuotientRankAtLeast for the kernel of `g(M)=M₁₂+M₂₁+M₂₂`. -/
theorem seed_ker_416 : QuotientRankAtLeast (kerEvalFunc (codeMat 416)) 6 :=
  contraction_seed_ker_invertible_minor (codeMat 416) 6 seed6 seed6
    (contractionMinor (codeMat 176) seed6 seed6) seed_minor_416_left_inverse

/-- QuotientRankAtLeast for the kernel of `f+g`. -/
theorem seed_ker_176 : QuotientRankAtLeast (kerEvalFunc (codeMat 176)) 6 :=
  contraction_seed_ker_invertible_minor (codeMat 176) 6 seed6 seed6
    (contractionMinor (codeMat 416) seed6 seed6) seed_minor_176_left_inverse

end QiushiMatmul
