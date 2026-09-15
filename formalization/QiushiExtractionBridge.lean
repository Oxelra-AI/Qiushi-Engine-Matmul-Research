import Mathlib
import QiushiDefs
import QiushiOccupationSoundness
import QiushiTotalWeight

/-!
# Generic extraction bridge for branch-tree occupation certificates

Bridges integer occupation no-model results to `QuotientRankAtLeast`.
Provides fiber-count infrastructure used by generated per-orbit modules.
-/

set_option maxHeartbeats 800000

open BigOperators Finset Matrix

attribute [local instance] Classical.propDecidable

noncomputable section

namespace QiushiMatmul

-- ============================================================================
-- Computational RREF reduction (used by generated per-orbit code)
-- ============================================================================

/-- Reduce a 9-bit matrix code modulo W using RREF elimination.
    basisPivots is [(basisCode₁, pivot₁), ...]. -/
def redCodeRREF (basisPivots : List (Nat × Nat)) (code : Nat) : Nat :=
  basisPivots.foldl (fun acc bp =>
    if (acc >>> bp.2) &&& 1 = 1 then acc ^^^ bp.1 else acc) code

-- ============================================================================
-- Fiber-count extraction from decomposition
-- ============================================================================

/-- The fiber cardinality for classification `classify` at value `label`. -/
def occFiberCard' {r n : ℕ} (classify : Fin r → Fin n) (label : Fin n) : ℕ :=
  (Finset.univ.filter (fun t : Fin r => classify t = label)).card

/-- Fiber counts sum to r. -/
theorem occFiberCard'_total {r n : ℕ} (classify : Fin r → Fin n) :
    ∑ label : Fin n, occFiberCard' classify label = r := by
  unfold occFiberCard'
  have h := Finset.card_eq_sum_card_fiberwise
    (f := classify) (s := Finset.univ (α := Fin r)) (t := Finset.univ (α := Fin n))
    (fun a _ => Finset.mem_univ (classify a))
  simp [Finset.card_univ, Fintype.card_fin] at h
  linarith

/-- Fibers for distinct labels are disjoint. -/
theorem occFiber_disjoint {r n : ℕ} (classify : Fin r → Fin n)
    (l₁ l₂ : Fin n) (hne : l₁ ≠ l₂) :
    Disjoint (Finset.univ.filter (fun t : Fin r => classify t = l₁))
             (Finset.univ.filter (fun t : Fin r => classify t = l₂)) := by
  rw [Finset.disjoint_filter]
  intro t _ h1 h2; exact hne (h1 ▸ h2)

-- ============================================================================
-- Label containment → fiber sum ≤ killSet card
-- ============================================================================

/-- If all terms classified into a label set lie in U, the sum of their
    fiber counts is bounded by |killSet D U|. -/
theorem labeled_fiber_sum_le_killSet {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    {r : ℕ} (D : QuotientTensorDecomp W r) {n : ℕ}
    (classify : Fin r → Fin n)
    (labels : Finset (Fin n))
    (hcontain : ∀ t : Fin r, classify t ∈ labels → D.A t ∈ U) :
    ∑ label ∈ labels, occFiberCard' classify label ≤ (killSet D U).card := by
  unfold occFiberCard'
  calc ∑ label ∈ labels,
      (Finset.univ.filter (fun t => classify t = label)).card
    = (labels.biUnion (fun label => Finset.univ.filter (fun t => classify t = label))).card := by
        rw [Finset.card_biUnion]
        intro l₁ _ l₂ _ hne
        exact occFiber_disjoint classify l₁ l₂ hne
    _ ≤ (killSet D U).card := by
        apply Finset.card_le_card
        apply Finset.biUnion_subset.mpr
        intro label hlabel t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
        simp only [killSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hcontain t (ht ▸ hlabel)

/-- Master row bound: labels in U, source lower bound m → sum ≤ target − m. -/
theorem labeled_fiber_occ_row {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    {r : ℕ} (D : QuotientTensorDecomp W r) {n : ℕ}
    (classify : Fin r → Fin n)
    (labels : Finset (Fin n))
    (hcontain : ∀ t : Fin r, classify t ∈ labels → D.A t ∈ U)
    {m : ℕ} (hm : QuotientRankAtLeast U m) (hmr : m ≤ r)
    {target : ℕ} (hrt : r ≤ target) :
    ∑ label ∈ labels, occFiberCard' classify label ≤ target - m :=
  le_trans (labeled_fiber_sum_le_killSet hWU D classify labels hcontain)
    (killSet_le_target hWU D hm hmr hrt)

-- ============================================================================
-- Int-cast occupation vector
-- ============================================================================

/-- Occupation vector: live label fiber counts cast to Int.
    Live labels are 1..nLive (label 0 is the W-coset).
    Variable j ∈ Fin nLive maps to label (j.val + 1). -/
def occVectorInt {r nLabels : ℕ} (classify : Fin r → Fin nLabels)
    (nLive : ℕ) (hLive : nLive + 1 ≤ nLabels) : Fin nLive → Int :=
  fun j => ↑(occFiberCard' classify ⟨j.val + 1, by omega⟩)

theorem occVectorInt_nonneg {r nLabels : ℕ} (classify : Fin r → Fin nLabels)
    {nLive : ℕ} (hLive : nLive + 1 ≤ nLabels) (j : Fin nLive) :
    0 ≤ occVectorInt classify nLive hLive j :=
  Int.natCast_nonneg _

/-- If the zero label has empty fiber, then the live-label occupation vector has
    exact total `r`.  Here `classify : Fin r → Fin (nLive+1)` uses label 0 for
    the killed W-coset and labels 1..nLive for live quotient labels. -/
theorem occVectorInt_total_of_zero {r nLive : ℕ}
    (classify : Fin r → Fin (nLive + 1))
    (hzero : occFiberCard' classify 0 = 0) :
    ∑ j : Fin nLive, occVectorInt classify nLive (Nat.le_refl _) j = (r : Int) := by
  have htot := occFiberCard'_total classify
  rw [Fin.sum_univ_succ] at htot
  simp [hzero] at htot
  change (∑ j : Fin nLive, (occFiberCard' classify j.succ : Int)) = (r : Int)
  exact_mod_cast htot

/-- Integer live-label version of `labeled_fiber_occ_row`.  A row's active set is
    expressed as live indices `Fin nLive`; the actual classifier labels are their
    successors in `Fin (nLive+1)`. -/
theorem live_labeled_fiber_occ_row_int {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    {r nLive : ℕ} (D : QuotientTensorDecomp W r)
    (classify : Fin r → Fin (nLive + 1))
    (activeSet : Finset (Fin nLive))
    (hcontain : ∀ t : Fin r, classify t ∈ activeSet.image Fin.succ → D.A t ∈ U)
    {m : ℕ} (hm : QuotientRankAtLeast U m) (hmr : m ≤ r)
    {target : ℕ} (hrt : r ≤ target) :
    (∑ j ∈ activeSet, occVectorInt classify nLive (Nat.le_refl _) j) ≤
      ((target - m : Nat) : Int) := by
  have hnat := labeled_fiber_occ_row hWU D classify (activeSet.image Fin.succ) hcontain hm hmr hrt
  have himg : ∑ label ∈ activeSet.image Fin.succ, occFiberCard' classify label =
      ∑ j ∈ activeSet, occFiberCard' classify (Fin.succ j) := by
    rw [Finset.sum_image]
    intro a _ b _ h
    exact Fin.succ_injective _ h
  rw [himg] at hnat
  change (∑ j ∈ activeSet, (occFiberCard' classify (Fin.succ j) : Int)) ≤
    ((target - m : Nat) : Int)
  exact_mod_cast hnat

-- ============================================================================
-- Master bridge theorem
-- ============================================================================

/-- **Branch extraction bridge.** If for every decomposition of length ≤ T
    we can extract an occupation vector satisfying S.RootHolds (using source
    lower bounds, fiber counts, and total weight), and the no-model proves
    RootHolds → False, then QuotientRankAtLeast W (T+1). -/
theorem branchBridge_quotientRankAtLeast
    (W : Submodule F2 Mat3) (T : ℕ)
    {nLive nOcc : ℕ}
    (S : OccSys nLive nOcc)
    (noModel : ∀ x : Fin nLive → Int, S.RootHolds x → False)
    (extractRootHolds : ∀ (r : ℕ), r ≤ T →
      ∀ D : QuotientTensorDecomp W r,
      ∃ x : Fin nLive → Int, S.RootHolds x) :
    QuotientRankAtLeast W (T + 1) := by
  apply quotientRankAtLeast_of_occupation_noModel W T
  intro r hr D
  rcases extractRootHolds r hr D with ⟨x, hx⟩
  exact noModel x hx

-- ============================================================================
-- RootHolds from label-filtered bounds
-- ============================================================================

/-- When coefficients are 0/1 matching a filter set, the weighted sum equals
    the filtered sum.  Used by generated bridge modules. -/
theorem weighted_sum_eq_filter_sum
    {nLive : ℕ}
    (coeff : Fin nLive → Int) (x : Fin nLive → Int)
    (S : Finset (Fin nLive))
    (hmatch : ∀ j, coeff j = if j ∈ S then 1 else 0) :
    ∑ j : Fin nLive, coeff j * x j = ∑ j ∈ S, x j := by
  have : ∀ j, coeff j * x j = if j ∈ S then x j else 0 := by
    intro j; rw [hmatch j]; split <;> simp
  simp_rw [this]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp [Finset.mem_filter]

/-- Construct `RootHolds` from label-filtered bounds.
    The generated bridge module proves per-row label bounds semantically;
    this lemma handles the coefficient conversion. -/
theorem rootHolds_from_label_bounds
    {nLive nOcc : ℕ} (S : OccSys nLive nOcc)
    (x : Fin nLive → Int)
    (hNonneg : ∀ j : Fin nLive, 0 ≤ x j)
    (hTotal : S.target ≤ ∑ j : Fin nLive, x j)
    -- Per-row data: active label set, bound proof, coefficient matching
    (activeSet : Fin nOcc → Finset (Fin nLive))
    (hBound : ∀ i : Fin nOcc, ∑ j ∈ activeSet i, x j ≤ S.occRhs i)
    (hCoeff : ∀ i : Fin nOcc, ∀ j : Fin nLive,
      S.occCoeff i j = if j ∈ activeSet i then 1 else 0)
    : S.RootHolds x where
  hOcc := fun i => by
    rw [weighted_sum_eq_filter_sum (S.occCoeff i) x (activeSet i) (hCoeff i)]
    exact hBound i
  hTotal := hTotal
  hNonneg := hNonneg

end QiushiMatmul
end
