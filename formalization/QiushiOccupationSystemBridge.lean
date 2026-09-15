import QiushiGenericPlaneExtraction

/-!
# Occupation-system reduction without tensor decompositions

Integer weights on matrix representatives are pushed through the checked code
classification. Dead-witness caps kill the entire zero-label weight. Source
caps then imply the reduced `OccSys.RootHolds` predicate.

The public quotient interface uses every actual nonzero element of `Mat3 / W`.
Over F2 these are the nonzero directions. No B/C completion, quotient tensor
decomposition, or source quotient-rank bound is a hypothesis. Identifying the
caps with a particular frozen L0 table remains a separate data-binding task.
-/

open BigOperators Finset Matrix

attribute [local instance] Classical.propDecidable

noncomputable section
namespace QiushiMatmul.OccupationSystemBridge

variable {ι : Type*} [Fintype ι]

/-- Weighted occupation of a matrix subspace, including multiplicities. -/
def matrixMass (A : ι → Mat3) (weight : ι → Int) (U : Submodule F2 Mat3) : Int :=
  ∑ t with A t ∈ U, weight t

/-- Weighted analogue of `occFiberCard'`, with no decomposition record. -/
def labelMass {n : Nat} (classify : ι → Fin n) (weight : ι → Int)
    (label : Fin n) : Int :=
  ∑ t with classify t = label, weight t

theorem labelMass_total {n : Nat} (classify : ι → Fin n) (weight : ι → Int) :
    ∑ label, labelMass classify weight label = ∑ t, weight t := by
  classical
  exact Finset.sum_fiberwise Finset.univ classify weight

theorem labelMass_selected_le {n : Nat} (classify : ι → Fin n)
    (A : ι → Mat3) (weight : ι → Int) (hNonneg : ∀ t, 0 ≤ weight t)
    (labels : Finset (Fin n)) (U : Submodule F2 Mat3)
    (hContain : ∀ t, classify t ∈ labels → A t ∈ U) :
    ∑ label ∈ labels, labelMass classify weight label ≤ matrixMass A weight U := by
  classical
  unfold labelMass matrixMass
  rw [Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro t ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hContain t (Finset.mem_filter.mp ht).2⟩
  · intro t _ _
    exact hNonneg t

/-- General weighted first-factor bridge. The weights may exceed one. -/
theorem matrix_counts_to_root
    (cfg : PlaneExtConfig) (hBool : PlaneExtBool cfg)
    (A : ι → Mat3) (weight : ι → Int)
    (hNonneg : ∀ t, 0 ≤ weight t)
    (hTotal : (cfg.target : Int) ≤ ∑ t, weight t)
    (hSource : ∀ i, matrixMass A weight (cfg.sourceU i) ≤
      (cfg.target : Int) - (cfg.sourceLb i : Int))
    (hDead : ∀ d, matrixMass A weight (cfg.deadU d) ≤ 0) :
    ∃ x : Fin cfg.nLive → Int, cfg.occSys.RootHolds x := by
  classical
  let classify : ι → Fin (cfg.nLive + 1) :=
    fun t => cfg.classifyCode (matrixCode (A t))
  have hZeroTerm : ∀ t, classify t = 0 → weight t = 0 := by
    intro t ht
    let c := matrixCode (A t)
    let d := cfg.deadCover c
    have hc : (cfg.classifyCode c).val = 0 := by
      simpa [classify, c] using congrArg Fin.val ht
    have hMem := spanContainsCode_implies_mem_spanCodes
      (cfg.deadBasis d) c.val (hBool.hDeadCover c hc)
    have hDecode : codeMat c.val = A t := codeMat_matrixCode (A t)
    rw [hDecode] at hMem
    have hLe : weight t ≤ matrixMass A weight (cfg.deadU d) := by
      apply Finset.single_le_sum
      · intro s _
        exact hNonneg s
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hMem⟩
    exact le_antisymm (hLe.trans (hDead d)) (hNonneg t)
  have hZero : labelMass classify weight 0 = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    exact hZeroTerm t (Finset.mem_filter.mp ht).2
  let x : Fin cfg.nLive → Int := fun j => labelMass classify weight j.succ
  have hTotalEq : ∑ j, x j = ∑ t, weight t := by
    have h := labelMass_total classify weight
    rw [Fin.sum_univ_succ, hZero, zero_add] at h
    exact h
  let activeSet : Fin cfg.nOcc → Finset (Fin cfg.nLive) := fun i =>
    Finset.univ.filter (fun j =>
      spanContainsCode (cfg.sourceBasis i) (cfg.sectionCode j).val = true)
  have hContain : ∀ i t,
      classify t ∈ (activeSet i).image Fin.succ → A t ∈ cfg.sourceU i := by
    intro i t ht
    rcases Finset.mem_image.mp ht with ⟨j, hj, hjLabel⟩
    have hjActive := (Finset.mem_filter.mp hj).2
    let c := matrixCode (A t)
    have hClass : cfg.classifyCode c = Fin.succ j := hjLabel.symm
    have hClassVal : (cfg.classifyCode c).val = j.val + 1 :=
      congrArg Fin.val hClass
    have hCosetW := spanContainsCode_implies_mem_spanCodes cfg.planeBasis
      (c.val ^^^ (cfg.sectionCode j).val) (hBool.hSectionCoset c j hClassVal)
    change codeMat (Nat.xor c.val (cfg.sectionCode j).val) ∈ cfg.W at hCosetW
    rw [codeMat_xor] at hCosetW
    have hCosetU := planeLeSource_of_bool (hBool.hPlaneLeSource i) hCosetW
    have hSectionU := spanContainsCode_implies_mem_spanCodes
      (cfg.sourceBasis i) (cfg.sectionCode j).val hjActive
    have hSum := (cfg.sourceU i).add_mem hCosetU hSectionU
    have hDecode : codeMat c.val = A t := codeMat_matrixCode (A t)
    rw [hDecode, add_assoc, mat3_add_self_eq_zero, add_zero] at hSum
    exact hSum
  refine ⟨x, rootHolds_from_label_bounds cfg.occSys x ?_ ?_ activeSet ?_ ?_⟩
  · intro j
    exact Finset.sum_nonneg (fun t _ => hNonneg t)
  · rw [hBool.hTarget, hTotalEq]
    exact hTotal
  · intro i
    have h := labelMass_selected_le classify A weight hNonneg
      ((activeSet i).image Fin.succ) (cfg.sourceU i) (hContain i)
    rw [Finset.sum_image (fun a _ b _ h => Fin.succ_injective _ h)] at h
    exact h.trans (by rw [hBool.hRhs]; exact hSource i)
  · intro i j
    rw [hBool.hIndicator]
    simp [activeSet]

/-- Actual nonzero quotient elements, not reduced live labels or support bits. -/
abbrev Direction (W : Submodule F2 Mat3) := {q : Mat3 ⧸ W // q ≠ 0}

instance directionFintype (W : Submodule F2 Mat3) : Fintype (Direction W) :=
  Fintype.ofFinite _

/-- Occupation of `U/W` by nonzero quotient directions. -/
def quotientMass {W : Submodule F2 Mat3} (weight : Direction W → Int)
    (U : Submodule F2 Mat3) : Int :=
  ∑ q with q.val ∈ U.map W.mkQ, weight q

theorem out_mem_iff {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    (q : Direction W) : q.val.out ∈ U ↔ q.val ∈ U.map W.mkQ := by
  have h := Submodule.comap_map_mkQ W U
  rw [sup_eq_right.mpr hWU] at h
  have hm : W.mkQ q.val.out = q.val := Submodule.Quotient.mk_out q.val
  have heq : q.val.out ∈ U ↔ W.mkQ q.val.out ∈ U.map W.mkQ := by
    change q.val.out ∈ U ↔ q.val.out ∈ Submodule.comap W.mkQ (U.map W.mkQ)
    rw [h]
  exact heq.trans (by rw [hm])

theorem matrixMass_out_eq {W U : Submodule F2 Mat3} (hWU : W ≤ U)
    (weight : Direction W → Int) :
    matrixMass (fun q : Direction W => q.val.out) weight U = quotientMass weight U := by
  classical
  simp only [matrixMass, quotientMass, out_mem_iff hWU]

/-- The full semantic cap interface needed by the reduced certificate. -/
structure Caps (cfg : PlaneExtConfig) (weight : Direction cfg.W → Int) : Prop where
  nonneg : ∀ q, 0 ≤ weight q
  total : (cfg.target : Int) ≤ ∑ q, weight q
  source : ∀ i, quotientMass weight (cfg.sourceU i) ≤
    (cfg.target : Int) - (cfg.sourceLb i : Int)
  dead : ∀ d, quotientMass weight (cfg.deadU d) ≤ 0

/-- Every integer solution on actual nonzero quotient directions reduces to a
solution of the live-label system. This does not assume tensor realizability. -/
theorem quotient_counts_to_root (cfg : PlaneExtConfig) (hBool : PlaneExtBool cfg)
    (weight : Direction cfg.W → Int) (h : Caps cfg weight) :
    ∃ x : Fin cfg.nLive → Int, cfg.occSys.RootHolds x := by
  apply matrix_counts_to_root cfg hBool (fun q => q.val.out) weight h.nonneg h.total
  · intro i
    rw [matrixMass_out_eq (planeLeSource_of_bool (hBool.hPlaneLeSource i))]
    exact h.source i
  · intro d
    rw [matrixMass_out_eq (planeLeDead_of_bool (hBool.hPlaneLeDead d))]
    exact h.dead d

theorem quotient_counts_no_model (cfg : PlaneExtConfig) (hBool : PlaneExtBool cfg)
    (hNoModel : ∀ x : Fin cfg.nLive → Int, cfg.occSys.RootHolds x → False)
    (weight : Direction cfg.W → Int) (h : Caps cfg weight) : False := by
  obtain ⟨x, hx⟩ := quotient_counts_to_root cfg hBool weight h
  exact hNoModel x hx

end QiushiMatmul.OccupationSystemBridge
