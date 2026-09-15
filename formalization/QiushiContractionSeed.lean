import Mathlib
import QiushiDefs
import QiushiOccupation
import QiushiOccupationAPI

/-!
# Contraction-seed bridge for flatten lower bounds

The contraction principle: if a linear functional `ℓ` on `Mat3` annihilates a
subspace `U`, then any quotient decomposition modulo `U` of length `r` induces
a bilinear decomposition of the contraction `M_ℓ(b,c) = ℓ(tensorASlice b c)`
of length at most `r`.  If `M_ℓ` contains a `k × k` identity submatrix, then
`r ≥ k`, giving `QuotientRankAtLeast U k`.
-/

set_option maxHeartbeats 16000000
open BigOperators Finset Matrix
namespace QiushiMatmul

-- ============================================================================
-- Linear functional on Mat3 (Frobenius inner product)
-- ============================================================================

/-- Frobenius inner product over F₂: `evalFunc L M = ∑ i j, L i j * M i j`. -/
def evalFunc (L : Mat3) (M : Mat3) : F2 :=
  ∑ i : I3, ∑ j : I3, L i j * M i j

/-- `evalFunc L` is additive. -/
theorem evalFunc_add (L M N : Mat3) :
    evalFunc L (M + N) = evalFunc L M + evalFunc L N := by
  unfold evalFunc
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  show L i j * (M + N) i j = L i j * M i j + L i j * N i j
  rw [show (M + N) i j = M i j + N i j from rfl, mul_add]

/-- `evalFunc L` respects scalar multiplication. -/
theorem evalFunc_smul (L : Mat3) (c : F2) (M : Mat3) :
    evalFunc L (c • M) = c * evalFunc L M := by
  unfold evalFunc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  show L i j * (c • M) i j = c * (L i j * M i j)
  simp [smul_eq_mul]; ring

/-- `evalFunc L` as a linear map. -/
def evalFuncLM (L : Mat3) : Mat3 →ₗ[F2] F2 where
  toFun M := evalFunc L M
  map_add' M N := evalFunc_add L M N
  map_smul' c M := by
    simp only [RingHom.id_apply]
    exact evalFunc_smul L c M

/-- `evalFunc L` commutes with finite sums. -/
theorem evalFunc_sum {ι : Type*} (L : Mat3) (s : Finset ι) (f : ι → Mat3) :
    evalFunc L (∑ t ∈ s, f t) = ∑ t ∈ s, evalFunc L (f t) :=
  map_sum (evalFuncLM L) f s

/-- Zero evaluates to zero. -/
theorem evalFunc_zero (L : Mat3) : evalFunc L 0 = 0 := by
  simp [evalFunc, mul_zero]

-- ============================================================================
-- Char-2 helper
-- ============================================================================

/-- In characteristic 2: `a + b = 0 → b = a`. -/
theorem eq_of_add_eq_zero_F2 (a b : F2) (h : a + b = 0) : b = a := by
  calc b = 0 + b := (zero_add b).symm
    _ = (a + a) + b := by rw [CharTwo.add_self_eq_zero a]
    _ = a + (a + b) := by rw [add_assoc]
    _ = a + 0 := by rw [h]
    _ = a := add_zero a

-- ============================================================================
-- Contraction identity
-- ============================================================================

/-- Contraction value: apply `evalFunc L` to a tensor A-slice. -/
def contractionVal (L : Mat3) (b c : Coord9) : F2 :=
  evalFunc L (tensorASlice b c)

/-- A selected square minor of the contraction matrix, using B-coordinates as rows
    and C-coordinates as columns. -/
def contractionMinor (L : Mat3) {k : ℕ} (rows cols : Fin k → Coord9) :
    Matrix (Fin k) (Fin k) F2 :=
  fun i j => contractionVal L (rows i) (cols j)

/-- **Contraction identity.** Applying `evalFunc L` to the quotient identity gives
    a bilinear expression: the contraction equals the weighted sum of B/C factors. -/
theorem contraction_identity
    {W : Submodule F2 Mat3} {r : ℕ}
    (D : QuotientTensorDecomp W r)
    (L : Mat3)
    (hKer : ∀ M : Mat3, M ∈ W → evalFunc L M = 0)
    (b c : Coord9) :
    contractionVal L b c =
      ∑ t : Fin r, D.B t b.1 b.2 * D.C t c.1 c.2 * evalFunc L (D.A t) := by
  have hQI := D.quotient_identity b c
  -- Apply evalFunc to the residual (which lies in W)
  have hRes : evalFunc L (tensorASlice b c +
      ∑ t : Fin r, (D.B t b.1 b.2 * D.C t c.1 c.2) • D.A t) = 0 :=
    hKer _ hQI
  -- Expand by additivity
  rw [evalFunc_add] at hRes
  -- Rewrite the sum part using linearity
  have hSumEq : evalFunc L (∑ t : Fin r, (D.B t b.1 b.2 * D.C t c.1 c.2) • D.A t) =
      ∑ t : Fin r, D.B t b.1 b.2 * D.C t c.1 c.2 * evalFunc L (D.A t) := by
    rw [evalFunc_sum L Finset.univ]
    apply Finset.sum_congr rfl; intro t _
    rw [evalFunc_smul]
  rw [hSumEq] at hRes
  -- From a + b = 0 derive a = b (char 2)
  exact (eq_of_add_eq_zero_F2 _ _ hRes).symm

-- ============================================================================
-- Factor bound (V * W = 1 over F₂ implies k ≤ r)
-- ============================================================================

/-- If `V * W = 1` over `F₂`, then `k ≤ r`. -/
theorem factor_bound {k r : ℕ}
    (V : Matrix (Fin k) (Fin r) F2)
    (W : Matrix (Fin r) (Fin k) F2)
    (h : V * W = 1) :
    k ≤ r := by
  have h1 : (V * W).rank ≤ V.rank := Matrix.rank_mul_le_left V W
  have h2 : V.rank ≤ r := Matrix.rank_le_width V
  have h3 : (V * W).rank = k := by rw [h, Matrix.rank_one, Fintype.card_fin]
  omega

-- ============================================================================
-- General contraction seed theorem
-- ============================================================================

/-- **Contraction seed.** If the contraction restricted to `k` coordinate pairs
    gives the identity matrix, then `QuotientRankAtLeast U k`. -/
theorem contraction_seed
    (U : Submodule F2 Mat3)
    (L : Mat3)
    (hKer : ∀ M : Mat3, M ∈ U → evalFunc L M = 0)
    (k : ℕ)
    (rows cols : Fin k → Coord9)
    (hDiag : ∀ i : Fin k, contractionVal L (rows i) (cols i) = 1)
    (hOffDiag : ∀ i j : Fin k, i ≠ j → contractionVal L (rows i) (cols j) = 0) :
    QuotientRankAtLeast U k := by
  intro r hr
  constructor
  intro D
  -- Build factor matrices from the bilinear decomposition
  let V : Matrix (Fin k) (Fin r) F2 :=
    fun i t => D.B t (rows i).1 (rows i).2 * evalFunc L (D.A t)
  let W : Matrix (Fin r) (Fin k) F2 :=
    fun t j => D.C t (cols j).1 (cols j).2
  -- Show V * W = 1 using the contraction identity
  have hVW : V * W = 1 := by
    ext i j
    -- First apply mul_apply to get the sum form, then unfold V/W
    rw [show (V * W) i j = ∑ t : Fin r, V i t * W t j from by simp [Matrix.mul_apply]]
    rw [show (1 : Matrix (Fin k) (Fin k) F2) i j = if i = j then 1 else 0 from by simp [Matrix.one_apply]]
    -- Rewrite sum in terms of D.B, D.C, evalFunc
    change ∑ t : Fin r,
        (D.B t (rows i).1 (rows i).2 * evalFunc L (D.A t)) *
        D.C t (cols j).1 (cols j).2 = if i = j then 1 else 0
    -- Rearrange to match contraction_identity output
    have hRewrite : ∀ t : Fin r,
        (D.B t (rows i).1 (rows i).2 * evalFunc L (D.A t)) *
        D.C t (cols j).1 (cols j).2 =
        D.B t (rows i).1 (rows i).2 * D.C t (cols j).1 (cols j).2 *
        evalFunc L (D.A t) := by intro t; ring
    simp_rw [hRewrite]
    rw [← contraction_identity D L hKer (rows i) (cols j)]
    by_cases hij : i = j
    · subst hij; simp [hDiag i]
    · simp [hij, hOffDiag i j hij]
  -- Apply factor bound: k ≤ r, contradicting r < k
  exact absurd (factor_bound V W hVW) (by omega)

/-- **Contraction seed with an invertible selected minor.** If a selected `k × k`
    contraction minor has a left inverse `Q`, then any quotient decomposition has
    length at least `k`. This is the right form when the contraction contains an
    invertible minor that is not literally an identity minor. -/
theorem contraction_seed_invertible_minor
    (U : Submodule F2 Mat3)
    (L : Mat3)
    (hKer : ∀ M : Mat3, M ∈ U → evalFunc L M = 0)
    (k : ℕ)
    (rows cols : Fin k → Coord9)
    (Q : Matrix (Fin k) (Fin k) F2)
    (hInv : Q * contractionMinor L rows cols = 1) :
    QuotientRankAtLeast U k := by
  intro r hr
  constructor
  intro D
  let V : Matrix (Fin k) (Fin r) F2 :=
    fun i t => D.B t (rows i).1 (rows i).2 * evalFunc L (D.A t)
  let W : Matrix (Fin r) (Fin k) F2 :=
    fun t j => D.C t (cols j).1 (cols j).2
  have hVW : V * W = contractionMinor L rows cols := by
    ext i j
    rw [show (V * W) i j = ∑ t : Fin r, V i t * W t j from by simp [Matrix.mul_apply]]
    change ∑ t : Fin r,
        (D.B t (rows i).1 (rows i).2 * evalFunc L (D.A t)) *
        D.C t (cols j).1 (cols j).2 = contractionVal L (rows i) (cols j)
    have hRewrite : ∀ t : Fin r,
        (D.B t (rows i).1 (rows i).2 * evalFunc L (D.A t)) *
        D.C t (cols j).1 (cols j).2 =
        D.B t (rows i).1 (rows i).2 * D.C t (cols j).1 (cols j).2 *
        evalFunc L (D.A t) := by intro t; ring
    simp_rw [hRewrite]
    rw [← contraction_identity D L hKer (rows i) (cols j)]
  have hQVW : (Q * V) * W = 1 := by
    rw [Matrix.mul_assoc, hVW, hInv]
  exact absurd (factor_bound (Q * V) W hQVW) (by omega)

/-- A selected square minor of the multi-functional contraction flattening.  A row
    is a pair `(s,b)`, where `s` selects a functional and `b` is a B-coordinate;
    a column is a C-coordinate. -/
def multiContractionMinor {q k : ℕ} (Ls : Fin q → Mat3)
    (rows : Fin k → Fin q × Coord9) (cols : Fin k → Coord9) :
    Matrix (Fin k) (Fin k) F2 :=
  fun i j => contractionVal (Ls (rows i).1) (rows i).2 (cols j)

/-- **Multi-functional contraction seed with an invertible selected minor.**
    Several functionals annihilating `U` may jointly yield a larger flattening
    rank lower bound than any single contraction. If a selected minor of the
    combined `(functional,B)`-by-`C` contraction flattening has a left inverse,
    then any quotient decomposition has length at least the minor size. -/
theorem multi_contraction_seed_invertible_minor
    (U : Submodule F2 Mat3)
    {q k : ℕ}
    (Ls : Fin q → Mat3)
    (hKer : ∀ s : Fin q, ∀ M : Mat3, M ∈ U → evalFunc (Ls s) M = 0)
    (rows : Fin k → Fin q × Coord9)
    (cols : Fin k → Coord9)
    (Q : Matrix (Fin k) (Fin k) F2)
    (hInv : Q * multiContractionMinor Ls rows cols = 1) :
    QuotientRankAtLeast U k := by
  intro r hr
  constructor
  intro D
  let V : Matrix (Fin k) (Fin r) F2 :=
    fun i t => D.B t (rows i).2.1 (rows i).2.2 *
      evalFunc (Ls (rows i).1) (D.A t)
  let W : Matrix (Fin r) (Fin k) F2 :=
    fun t j => D.C t (cols j).1 (cols j).2
  have hVW : V * W = multiContractionMinor Ls rows cols := by
    ext i j
    rw [show (V * W) i j = ∑ t : Fin r, V i t * W t j from by simp [Matrix.mul_apply]]
    change ∑ t : Fin r,
        (D.B t (rows i).2.1 (rows i).2.2 * evalFunc (Ls (rows i).1) (D.A t)) *
        D.C t (cols j).1 (cols j).2 = contractionVal (Ls (rows i).1) (rows i).2 (cols j)
    have hRewrite : ∀ t : Fin r,
        (D.B t (rows i).2.1 (rows i).2.2 * evalFunc (Ls (rows i).1) (D.A t)) *
        D.C t (cols j).1 (cols j).2 =
        D.B t (rows i).2.1 (rows i).2.2 * D.C t (cols j).1 (cols j).2 *
        evalFunc (Ls (rows i).1) (D.A t) := by intro t; ring
    simp_rw [hRewrite]
    rw [← contraction_identity D (Ls (rows i).1) (hKer (rows i).1) (rows i).2 (cols j)]
  have hQVW : (Q * V) * W = 1 := by
    rw [Matrix.mul_assoc, hVW, hInv]
  exact absurd (factor_bound (Q * V) W hQVW) (by omega)

-- ============================================================================
-- Kernel submodule from a functional
-- ============================================================================

/-- Kernel of `evalFunc L` as a submodule of `Mat3`. -/
def kerEvalFunc (L : Mat3) : Submodule F2 Mat3 where
  carrier := {M | evalFunc L M = 0}
  zero_mem' := evalFunc_zero L
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [evalFunc_add, ha, hb, add_zero]
  smul_mem' c {M} hM := by
    simp only [Set.mem_setOf_eq] at *
    rw [evalFunc_smul, hM, mul_zero]

theorem mem_kerEvalFunc (L M : Mat3) : M ∈ kerEvalFunc L ↔ evalFunc L M = 0 :=
  Iff.rfl

/-- `contraction_seed` applied to a kernel submodule. -/
theorem contraction_seed_ker
    (L : Mat3) (k : ℕ)
    (rows cols : Fin k → Coord9)
    (hDiag : ∀ i : Fin k, contractionVal L (rows i) (cols i) = 1)
    (hOffDiag : ∀ i j : Fin k, i ≠ j → contractionVal L (rows i) (cols j) = 0) :
    QuotientRankAtLeast (kerEvalFunc L) k :=
  contraction_seed (kerEvalFunc L) L (fun M hM => hM) k rows cols hDiag hOffDiag

/-- `contraction_seed_invertible_minor` applied to a kernel submodule. -/
theorem contraction_seed_ker_invertible_minor
    (L : Mat3) (k : ℕ)
    (rows cols : Fin k → Coord9)
    (Q : Matrix (Fin k) (Fin k) F2)
    (hInv : Q * contractionMinor L rows cols = 1) :
    QuotientRankAtLeast (kerEvalFunc L) k :=
  contraction_seed_invertible_minor (kerEvalFunc L) L (fun M hM => hM) k rows cols Q hInv

/-- `multi_contraction_seed_invertible_minor` applied when `U` lies in all
    participating functional kernels. -/
theorem multi_contraction_seed_of_le_kernels
    (U : Submodule F2 Mat3)
    {q k : ℕ}
    (Ls : Fin q → Mat3)
    (hLe : ∀ s : Fin q, U ≤ kerEvalFunc (Ls s))
    (rows : Fin k → Fin q × Coord9)
    (cols : Fin k → Coord9)
    (Q : Matrix (Fin k) (Fin k) F2)
    (hInv : Q * multiContractionMinor Ls rows cols = 1) :
    QuotientRankAtLeast U k :=
  multi_contraction_seed_invertible_minor U Ls (fun s M hM => hLe s hM)
    rows cols Q hInv

-- ============================================================================
-- Complementary (functional,C)×B orientation
-- ============================================================================

/-- CB contraction minor: rows are `(s, c)` pairs (functional index × C-coordinate),
    columns are B-coordinates.  Entry `(i,j) = contractionVal (Ls (rows i).1) (cols j) (rows i).2`. -/
def multiContractionMinorCB {q k : ℕ} (Ls : Fin q → Mat3)
    (rows : Fin k → Fin q × Coord9) (cols : Fin k → Coord9) :
    Matrix (Fin k) (Fin k) F2 :=
  fun i j => contractionVal (Ls (rows i).1) (cols j) (rows i).2

/-- **CB multi-functional contraction seed.** The complementary orientation factors
    the contraction decomposition through `C_t · evalFunc` and `B_t` instead of
    `B_t · evalFunc` and `C_t`.  An invertible minor in this orientation provides
    the same rank lower bound. -/
theorem multi_contraction_seed_CB_invertible_minor
    (U : Submodule F2 Mat3)
    {q k : ℕ}
    (Ls : Fin q → Mat3)
    (hKer : ∀ s : Fin q, ∀ M : Mat3, M ∈ U → evalFunc (Ls s) M = 0)
    (rows : Fin k → Fin q × Coord9)
    (cols : Fin k → Coord9)
    (Q : Matrix (Fin k) (Fin k) F2)
    (hInv : Q * multiContractionMinorCB Ls rows cols = 1) :
    QuotientRankAtLeast U k := by
  intro r hr
  constructor
  intro D
  let V : Matrix (Fin k) (Fin r) F2 :=
    fun i t => D.C t (rows i).2.1 (rows i).2.2 *
      evalFunc (Ls (rows i).1) (D.A t)
  let W : Matrix (Fin r) (Fin k) F2 :=
    fun t j => D.B t (cols j).1 (cols j).2
  have hVW : V * W = multiContractionMinorCB Ls rows cols := by
    ext i j
    rw [show (V * W) i j = ∑ t : Fin r, V i t * W t j from by simp [Matrix.mul_apply]]
    change ∑ t : Fin r,
        (D.C t (rows i).2.1 (rows i).2.2 * evalFunc (Ls (rows i).1) (D.A t)) *
        D.B t (cols j).1 (cols j).2 = contractionVal (Ls (rows i).1) (cols j) (rows i).2
    have hRewrite : ∀ t : Fin r,
        (D.C t (rows i).2.1 (rows i).2.2 * evalFunc (Ls (rows i).1) (D.A t)) *
        D.B t (cols j).1 (cols j).2 =
        D.B t (cols j).1 (cols j).2 * D.C t (rows i).2.1 (rows i).2.2 *
        evalFunc (Ls (rows i).1) (D.A t) := by intro t; ring
    simp_rw [hRewrite]
    rw [← contraction_identity D (Ls (rows i).1) (hKer (rows i).1) (cols j) (rows i).2]
  have hQVW : (Q * V) * W = 1 := by
    rw [Matrix.mul_assoc, hVW, hInv]
  exact absurd (factor_bound (Q * V) W hQVW) (by omega)

/-- CB contraction seed when `U` lies in all participating functional kernels. -/
theorem multi_contraction_seed_CB_of_le_kernels
    (U : Submodule F2 Mat3)
    {q k : ℕ}
    (Ls : Fin q → Mat3)
    (hLe : ∀ s : Fin q, U ≤ kerEvalFunc (Ls s))
    (rows : Fin k → Fin q × Coord9)
    (cols : Fin k → Coord9)
    (Q : Matrix (Fin k) (Fin k) F2)
    (hInv : Q * multiContractionMinorCB Ls rows cols = 1) :
    QuotientRankAtLeast U k :=
  multi_contraction_seed_CB_invertible_minor U Ls (fun s M hM => hLe s hM)
    rows cols Q hInv

end QiushiMatmul
