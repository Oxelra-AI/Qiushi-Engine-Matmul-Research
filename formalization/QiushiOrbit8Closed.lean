import QiushiOrbit8Seeds
import QiushiWeightedCover

/-!
# Closed orbit-8 pilot for the weighted-cover source route

This module proves the small but fully semantic pilot bound
`QuotientRankAtLeast orbit8W 9`.

The proof uses three actual source kernels:
`ker(codeMat 272)`, `ker(codeMat 416)`, and `ker(codeMat 176)`.  Each has
quotient rank at least 6 by the contraction seeds.  The three kernels cover every
A-factor because over `F₂` one of `f(M)`, `g(M)`, and `f(M)+g(M)` is zero.  The
all-ones weighted-cover inequality then excludes every length `r ≤ 8` quotient
decomposition modulo `orbit8W`.
-/

set_option maxHeartbeats 16000000
open BigOperators Finset Matrix
namespace QiushiMatmul

/-- The qdim-2 orbit-8 subspace used in the closed pilot. -/
def orbit8W : Submodule F2 Mat3 := spanCodes [304, 160, 64, 8, 4, 2, 1]

/-- Generic helper: if a functional vanishes on the listed code generators, then
it vanishes on their span. -/
theorem spanCodes_le_kerEvalFunc_of_gens (L : Mat3) (xs : List Nat)
    (hgens : ∀ n : Nat, n ∈ xs → evalFunc L (codeMat n) = 0) :
    spanCodes xs ≤ kerEvalFunc L := by
  intro M hM
  change evalFunc L M = 0
  refine Submodule.span_induction (p := fun x _ => evalFunc L x = 0) ?_ ?_ ?_ ?_ hM
  · intro x hx
    rcases hx with ⟨n, hn, rfl⟩
    exact hgens n hn
  · exact evalFunc_zero L
  · intro x y _ _ hx hy
    rw [evalFunc_add, hx, hy, add_zero]
  · intro a x _ hx
    rw [evalFunc_smul, hx, mul_zero]

lemma orbit8_gens_annihilated_272 (n : Nat)
    (hn : n ∈ [304, 160, 64, 8, 4, 2, 1]) :
    evalFunc (codeMat 272) (codeMat n) = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with hn | hn | hn | hn | hn | hn | hn <;> subst hn <;> decide

lemma orbit8_gens_annihilated_416 (n : Nat)
    (hn : n ∈ [304, 160, 64, 8, 4, 2, 1]) :
    evalFunc (codeMat 416) (codeMat n) = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with hn | hn | hn | hn | hn | hn | hn <;> subst hn <;> decide

lemma orbit8_gens_annihilated_176 (n : Nat)
    (hn : n ∈ [304, 160, 64, 8, 4, 2, 1]) :
    evalFunc (codeMat 176) (codeMat n) = 0 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with hn | hn | hn | hn | hn | hn | hn <;> subst hn <;> decide

/-- `orbit8W` is contained in the kernel of `codeMat 272`. -/
theorem orbit8W_le_ker_272 : orbit8W ≤ kerEvalFunc (codeMat 272) :=
  spanCodes_le_kerEvalFunc_of_gens (codeMat 272) [304, 160, 64, 8, 4, 2, 1]
    orbit8_gens_annihilated_272

/-- `orbit8W` is contained in the kernel of `codeMat 416`. -/
theorem orbit8W_le_ker_416 : orbit8W ≤ kerEvalFunc (codeMat 416) :=
  spanCodes_le_kerEvalFunc_of_gens (codeMat 416) [304, 160, 64, 8, 4, 2, 1]
    orbit8_gens_annihilated_416

/-- `orbit8W` is contained in the kernel of `codeMat 176`. -/
theorem orbit8W_le_ker_176 : orbit8W ≤ kerEvalFunc (codeMat 176) :=
  spanCodes_le_kerEvalFunc_of_gens (codeMat 176) [304, 160, 64, 8, 4, 2, 1]
    orbit8_gens_annihilated_176

/-- Addition in the coefficient matrix slot of `evalFunc`. -/
theorem evalFunc_add_left (L N M : Mat3) :
    evalFunc (L + N) M = evalFunc L M + evalFunc N M := by
  unfold evalFunc
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  show (L + N) i j * M i j = L i j * M i j + N i j * M i j
  rw [show (L + N) i j = L i j + N i j from rfl, add_mul]

lemma codeMat176_eq_272_add_416 :
    codeMat 176 = codeMat 272 + codeMat 416 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- Over `F₂`, among `a`, `b`, and `a+b` at least one is zero. -/
lemma F2_three_zero (a b : F2) : a = 0 ∨ b = 0 ∨ a + b = 0 := by
  decide +revert

/-- Over `F₂`, one of `f(M)`, `g(M)`, and `f(M)+g(M)` is zero; here
`codeMat 176` is exactly the coefficient matrix for `f+g`. -/
theorem orbit8_three_kernel_coverage (M : Mat3) :
    M ∈ kerEvalFunc (codeMat 272) ∨
    M ∈ kerEvalFunc (codeMat 416) ∨
    M ∈ kerEvalFunc (codeMat 176) := by
  change evalFunc (codeMat 272) M = 0 ∨
      evalFunc (codeMat 416) M = 0 ∨ evalFunc (codeMat 176) M = 0
  have h176 : evalFunc (codeMat 176) M =
      evalFunc (codeMat 272) M + evalFunc (codeMat 416) M := by
    rw [codeMat176_eq_272_add_416, evalFunc_add_left]
  have htri : evalFunc (codeMat 272) M = 0 ∨
      evalFunc (codeMat 416) M = 0 ∨
      evalFunc (codeMat 272) M + evalFunc (codeMat 416) M = 0 :=
    F2_three_zero (evalFunc (codeMat 272) M) (evalFunc (codeMat 416) M)
  rcases htri with h0 | h1 | h2
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (by rw [h176, h2]))

/-- The three source kernels used by the orbit-8 weighted-cover pilot. -/
def orbit8SourceU : Fin 3 → Submodule F2 Mat3
  | ⟨0, _⟩ => kerEvalFunc (codeMat 272)
  | ⟨1, _⟩ => kerEvalFunc (codeMat 416)
  | ⟨2, _⟩ => kerEvalFunc (codeMat 176)

theorem orbit8W_le_sourceU (i : Fin 3) : orbit8W ≤ orbit8SourceU i := by
  fin_cases i <;> simp [orbit8SourceU, orbit8W_le_ker_272, orbit8W_le_ker_416,
    orbit8W_le_ker_176]

theorem orbit8SourceU_lb6 (i : Fin 3) : QuotientRankAtLeast (orbit8SourceU i) 6 := by
  fin_cases i <;> simp [orbit8SourceU, seed_ker_272, seed_ker_416, seed_ker_176]

lemma one_le_sum_if_mem {r : ℕ} (kill : Fin 3 → Finset (Fin r))
    (t : Fin r) (i0 : Fin 3) (ht : t ∈ kill i0) :
    1 ≤ ∑ i : Fin 3, if t ∈ kill i then (1 : ℕ) else 0 := by
  calc
    1 ≤ (if t ∈ kill i0 then (1 : ℕ) else 0) := by simp [ht]
      _ ≤ ∑ i : Fin 3, if t ∈ kill i then (1 : ℕ) else 0 := by
        exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
          (a := i0)
          (f := fun i : Fin 3 => if t ∈ kill i then (1 : ℕ) else 0)
          (fun i _ => by by_cases h : t ∈ kill i <;> simp [h])
          (Finset.mem_univ i0)

/-- No quotient decomposition of `orbit8W` of length `r < 9`. -/
theorem orbit8_false_of_lt9 {r : ℕ} (hr : r < 9)
    (D : QuotientTensorDecomp orbit8W r) : False := by
  by_cases hsmall : r < 6
  · exact quotient_bound_exceeds_length orbit8W_le_ker_272 D seed_ker_272 hsmall
  · have h6 : 6 ≤ r := Nat.le_of_not_gt hsmall
    have hrt : r ≤ 8 := by omega
    let kill : Fin 3 → Finset (Fin r) := fun i => killSet D (orbit8SourceU i)
    have hRowsAdd : ∀ i : Fin 3, (kill i).card + 6 ≤ r := by
      intro i
      have hk : (killSet D (orbit8SourceU i)).card ≤ r - 6 :=
        occupation_inequality (orbit8W_le_sourceU i) D (orbit8SourceU_lb6 i) h6
      change (killSet D (orbit8SourceU i)).card + 6 ≤ r
      omega
    have hCoverage : ∀ t : Fin r,
        1 ≤ ∑ i : Fin 3, if t ∈ kill i then (1 : ℕ) else 0 := by
      intro t
      rcases orbit8_three_kernel_coverage (D.A t) with h272 | hrest
      · have ht : t ∈ kill (0 : Fin 3) := by
          change t ∈ killSet D (kerEvalFunc (codeMat 272))
          simp only [killSet, Finset.mem_filter, Finset.mem_univ, true_and]
          exact h272
        exact one_le_sum_if_mem kill t (0 : Fin 3) ht
      · rcases hrest with h416 | h176
        · have ht : t ∈ kill (1 : Fin 3) := by
            change t ∈ killSet D (kerEvalFunc (codeMat 416))
            simp only [killSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact h416
          exact one_le_sum_if_mem kill t (1 : Fin 3) ht
        · have ht : t ∈ kill (2 : Fin 3) := by
            change t ∈ killSet D (kerEvalFunc (codeMat 176))
            simp only [killSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact h176
          exact one_le_sum_if_mem kill t (2 : Fin 3) ht
    have hLambda : 1 ≤ ∑ i : Fin 3, (1 : ℕ) := by decide
    have hCert : ((∑ i : Fin 3, (1 : ℕ)) - 1) * 8 <
        ∑ i : Fin 3, (1 : ℕ) * 6 := by decide
    exact weighted_cover_infeasible_from_term_coverage kill (fun _ : Fin 3 => 6)
      (fun _ : Fin 3 => 1) 1 8 hLambda hCoverage hRowsAdd hrt hCert

/-- Closed orbit-8 pilot lower bound. -/
theorem orbit8_lb9 : QuotientRankAtLeast orbit8W 9 :=
  quotientRankAtLeast_of_contradiction orbit8W 9 (fun r hr D => orbit8_false_of_lt9 hr D)

end QiushiMatmul
