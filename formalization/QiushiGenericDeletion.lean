import QiushiForcedProductBound
import QiushiQuotientToSliceFamily
import QiushiContractionSeed

/-!
# Generic k-fold deletion bound for forced-product seeds

`no_short_of_deletions k f`: k B-slot deletions + f-column fold-uniform base
gives length ≥ k + f for any `BSliceFamilyDecomp`.  Orbit modules supply only
finite data: `SelectedIndependent` and `FoldUniformWitness`.
-/

open BigOperators Finset

set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace QiushiMatmul

-- ============================================================================
-- Shared definitions
-- ============================================================================

variable {β γ V : Type*} [AddCommGroup V] [Module F2 V]

/-- Selected B-slices are independent: every nonzero linear combination
is nonzero at some C-coordinate. -/
def SelectedIndependent {k : ℕ} (S : β → γ → V) (sels : Fin k → β) : Prop :=
  ∀ z : Fin k → F2, z ≠ 0 → ∃ c : γ, (∑ l : Fin k, z l • S (sels l) c) ≠ 0

-- ============================================================================
-- Generic coordinate map
-- ============================================================================

/-- Generic coordinate map from annihilator functionals. -/
def piOfLs {q : ℕ} (Ls : Fin q → Mat3) : Mat3 →ₗ[F2] (Fin q → F2) where
  toFun M := fun i => evalFunc (Ls i) M
  map_add' M N := by ext i; exact evalFunc_add (Ls i) M N
  map_smul' a M := by ext i; simp only [Pi.smul_apply]; exact evalFunc_smul (Ls i) a M

/-- `piOfLs` annihilates generators → annihilates the whole span. -/
theorem piOfLs_kills_span {q : ℕ} (Ls : Fin q → Mat3) (codes : List Nat)
    (h : ∀ n, n ∈ codes → piOfLs Ls (codeMat n) = 0)
    (X : Mat3) (hX : X ∈ spanCodes codes) : piOfLs Ls X = 0 := by
  unfold spanCodes at hX
  refine Submodule.span_induction (p := fun X _ => piOfLs Ls X = 0) ?_ ?_ ?_ ?_ hX
  · intro Y hY; rcases hY with ⟨n, hn, rfl⟩; exact h n hn
  · ext i; simp [piOfLs, evalFunc]
  · intro X Y _ _ hX hY; rw [map_add, hX, hY, add_zero]
  · intro a X _ hX; rw [map_smul, hX, smul_zero]

-- ============================================================================
-- Key lemma: fold preserves tail independence
-- ============================================================================

variable [Fintype β] [Fintype γ]

/-- After one B-slot fold at `sels 0` with shear `g`, the tail slices
remain independent. -/
theorem selected_independent_fold_tail
    {k : ℕ} (S : β → γ → V) (sels : Fin (k + 1) → β)
    (hInd : SelectedIndependent S sels) (g : β → F2) :
    SelectedIndependent (fun b c => S b c + g b • S (sels 0) c)
      (fun l => sels (Fin.succ l)) := by
  intro z hz
  let a : F2 := ∑ l : Fin k, z l * g (sels (Fin.succ l))
  let z' : Fin (k + 1) → F2 := Fin.cons a z
  have hz' : z' ≠ 0 := by
    intro h; apply hz; ext l
    have := congr_fun h (Fin.succ l)
    simp only [z', Fin.cons_succ] at this; exact this
  obtain ⟨c, hc⟩ := hInd z' hz'
  refine ⟨c, fun heq => hc ?_⟩
  -- Key identity: ∑ z'_l • S(sels l) = ∑ z_l • fold(sels(l+1))
  calc ∑ l : Fin (k + 1), z' l • S (sels l) c
      = a • S (sels 0) c + ∑ l : Fin k, z l • S (sels (Fin.succ l)) c := by
        rw [Fin.sum_univ_succ]; simp only [z', Fin.cons_zero, Fin.cons_succ]
    _ = ∑ l : Fin k, z l • S (sels (Fin.succ l)) c + a • S (sels 0) c := by
        abel
    _ = ∑ l : Fin k, z l • S (sels (Fin.succ l)) c +
        ∑ l : Fin k, (z l * g (sels (Fin.succ l))) • S (sels 0) c := by
        congr 1
        show a • S (sels 0) c = _
        rw [show a = ∑ l : Fin k, z l * g (sels (Fin.succ l)) from rfl,
            Finset.sum_smul]
    _ = ∑ l : Fin k, (z l • S (sels (Fin.succ l)) c +
        (z l * g (sels (Fin.succ l))) • S (sels 0) c) := by
        rw [← Finset.sum_add_distrib]
    _ = ∑ l : Fin k, z l • (S (sels (Fin.succ l)) c +
        g (sels (Fin.succ l)) • S (sels 0) c) := by
        congr 1; ext l; rw [mul_smul, ← smul_add]
    _ = 0 := heq

-- ============================================================================
-- Generic k-fold deletion bound
-- ============================================================================

/-- Generic k-fold deletion bound by induction on `k`. -/
theorem no_short_of_deletions :
    ∀ (k f : ℕ) (S : β → γ → V) (sels : Fin k → β) (cols : Fin f → γ),
      SelectedIndependent S sels → FoldUniformWitness S sels cols →
      ∀ r, r < k + f → BSliceFamilyDecomp S r → False := by
  intro k
  induction k with
  | zero =>
    intro f S sels cols _hInd hFK r hr D
    have hbase : ∀ y : Fin f → F2, y ≠ 0 →
        ∃ (b : β) (phi : V →ₗ[F2] F2), phi (∑ j, y j • S b (cols j)) ≠ 0 := by
      intro y hy; obtain ⟨b, phi, _, hdet⟩ := hFK y hy; exact ⟨b, phi, hdet⟩
    exact absurd (show r < f from by omega)
      (not_lt.mpr (fold_uniform_base_bound D cols hbase))
  | succ k' ih =>
    intro f S sels cols hInd hFK r hr D
    -- Nonzero slice at sels 0
    have hNZ : ∃ c : γ, S (sels 0) c ≠ 0 := by
      let z : Fin (k' + 1) → F2 := Fin.cons 1 0
      have hz : z ≠ 0 := by
        intro h; have h0 := congr_fun h 0; simp [z, Fin.cons_zero] at h0
      obtain ⟨c, hc⟩ := hInd z hz
      refine ⟨c, fun h => hc ?_⟩
      rw [Fin.sum_univ_succ]
      simp [z, Fin.cons_zero, Fin.cons_succ, h]
    cases r with
    | zero =>
      obtain ⟨c, hc⟩ := hNZ
      obtain ⟨t, _⟩ := exists_b_active_of_slice_ne_zero D hc
      exact Fin.elim0 t
    | succ r' =>
      obtain ⟨c, hc⟩ := hNZ
      obtain ⟨t0, ht0⟩ := exists_b_active_of_slice_ne_zero D hc
      -- Apply IH to the folded family
      have hfold : foldedBFamily D t0 (sels 0) =
          fun b c => S b c + D.B t0 b • S (sels 0) c := by
        ext b c; rfl
      exact ih f (foldedBFamily D t0 (sels 0))
        (fun l => sels (Fin.succ l)) cols
        (hfold ▸ selected_independent_fold_tail S sels hInd (D.B t0))
        (fold_uniform_witness_transfer sels cols (D.B t0) hFK
          (foldedBFamily D t0 (sels 0)) (fun b c => by unfold foldedBFamily; rfl))
        r' (by omega) (deleteBDecomp D t0 (sels 0) ht0)

-- ============================================================================
-- Decidable-to-abstract lifting: coordinate projections
-- ============================================================================

/-- Coordinate projection on `Fin q → F2`. -/
def vProj {q : ℕ} (i : Fin q) : (Fin q → F2) →ₗ[F2] F2 where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Finite form of smul-sum components for piOfLs-style families. -/
private theorem sum_smul_component {q n : ℕ} {β : Type*}
    (S : β → (Fin q → F2)) (z : Fin n → F2) (sels : Fin n → β) (i : Fin q) :
    (∑ l : Fin n, z l • S (sels l)) i = ∑ l : Fin n, z l * S (sels l) i := by
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Lift a component-level independence check (decidable) to
`SelectedIndependent` (using abstract smul). -/
theorem selected_independent_of_fin_check {q k : ℕ}
    (S : Coord9 → Coord9 → (Fin q → F2))
    (sels : Fin k → Coord9)
    (h : ∀ z : Fin k → F2, z ≠ 0 →
        ∃ (c : Coord9) (i : Fin q),
          ∑ l : Fin k, z l * S (sels l) c i ≠ 0) :
    SelectedIndependent S sels := by
  intro z hz
  obtain ⟨c, i, hi⟩ := h z hz
  refine ⟨c, fun heq => hi ?_⟩
  have h0 : (∑ l : Fin k, z l • S (sels l) c) i = 0 := by rw [heq]; rfl
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h0

/-- Lift a component-level fold-uniform witness check (decidable) to
`FoldUniformWitness` (using abstract linear maps). -/
theorem fold_uniform_witness_of_fin_check {q k f : ℕ}
    (S : Coord9 → Coord9 → (Fin q → F2))
    (sels : Fin k → Coord9) (cols : Fin f → Coord9)
    (h : ∀ y : Fin f → F2, y ≠ 0 →
        ∃ (b : Coord9) (i : Fin q),
          (∀ l : Fin k, ∑ j : Fin f, y j * S (sels l) (cols j) i = 0) ∧
          (∑ j : Fin f, y j * S b (cols j) i ≠ 0)) :
    FoldUniformWitness S sels cols := by
  intro y hy
  obtain ⟨b, i, hann, hdet⟩ := h y hy
  refine ⟨b, vProj i, fun l => ?_, ?_⟩
  · -- phi (∑ y_j • S (sels l) (cols j)) = 0
    show (∑ j : Fin f, y j • S (sels l) (cols j)) i = 0
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hann l
  · -- phi (∑ y_j • S b (cols j)) ≠ 0
    show (∑ j : Fin f, y j • S b (cols j)) i ≠ 0
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hdet

end QiushiMatmul
