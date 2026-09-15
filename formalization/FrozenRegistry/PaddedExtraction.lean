import QiushiGenericPlaneExtraction

open BigOperators

namespace QiushiMatmul.FrozenRegistry

/-- Padded extraction uses all nonzero quotient labels. It needs no rank
assumption for the zero fiber or for the configuration's dead-witness fields. -/
theorem padded_plane_qra (cfg : PlaneExtConfig) (hBool : PlaneExtBool cfg)
    (hZero : ∀ c : Fin 512, (cfg.classifyCode c).val = 0 →
      spanContainsCode cfg.planeBasis c.val = true)
    (pad : Fin cfg.nLive)
    (hSource : ∀ i : Fin cfg.nOcc,
      QuotientRankAtLeast (cfg.sourceU i) (cfg.sourceLb i))
    (hNoModel : ∀ x : Fin cfg.nLive → Int, cfg.occSys.RootHolds x → False) :
    QuotientRankAtLeast cfg.W (cfg.target + 1) := by
  classical
  have hLe : ∀ i : Fin cfg.nOcc, cfg.W ≤ cfg.sourceU i := fun i =>
    planeLeSource_of_bool (fun g hg => hBool.hPlaneLeSource i g hg)
  intro r hr
  refine ⟨fun D => ?_⟩
  have hrt : r ≤ cfg.target := by omega
  let classify : Fin r → Fin (cfg.nLive + 1) :=
    fun t => cfg.classifyCode (matrixCode (D.A t))
  let x := occVectorIntPadded classify cfg.target pad
  let active : Fin cfg.nOcc → Finset (Fin cfg.nLive) := fun i =>
    Finset.univ.filter (fun j =>
      spanContainsCode (cfg.sourceBasis i) (cfg.sectionCode j).val = true)
  have hzero : ∀ (i : Fin cfg.nOcc) (t : Fin r), classify t = 0 →
      D.A t ∈ cfg.sourceU i := by
    intro i t ht
    have hcode := hZero (matrixCode (D.A t)) (congrArg Fin.val ht)
    have hmem := spanContainsCode_implies_mem_spanCodes _ _ hcode
    apply hLe i
    simpa only [matrixCode, codeMat_matrixCode] using hmem
  have hcontain : ∀ (i : Fin cfg.nOcc) (t : Fin r),
      classify t ∈ (active i).image Fin.succ → D.A t ∈ cfg.sourceU i := by
    intro i t ht
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp ht
    have hsection := spanContainsCode_implies_mem_spanCodes _ _
      ((Finset.mem_filter.mp hj).2)
    let c := matrixCode (D.A t)
    have hclass : (cfg.classifyCode c).val = j.val + 1 := by
      simpa [classify, c] using congrArg Fin.val heq.symm
    have hcoset := spanContainsCode_implies_mem_spanCodes _ _
      (hBool.hSectionCoset c j hclass)
    change codeMat (Nat.xor c.val (cfg.sectionCode j).val) ∈ cfg.W at hcoset
    rw [codeMat_xor] at hcoset
    have hsum := (cfg.sourceU i).add_mem (hLe i hcoset) hsection
    have hdecode : codeMat c.val = D.A t := by
      simpa [c, matrixCode] using codeMat_matrixCode (D.A t)
    rw [hdecode, add_assoc, mat3_add_self_eq_zero, add_zero] at hsum
    exact hsum
  have hbound : ∀ i : Fin cfg.nOcc, ∑ j ∈ active i, x j ≤ cfg.occSys.occRhs i := by
    intro i
    by_cases hm : cfg.sourceLb i ≤ cfg.target
    · have h := live_labeled_fiber_occ_row_int_padded (hLe i) D classify
        (active i) (hzero i) (hcontain i) (hSource i) hrt pad
      have hcast : ((cfg.target - cfg.sourceLb i : Nat) : Int) =
          (cfg.target : Int) - (cfg.sourceLb i : Int) := by omega
      rw [hcast, ← hBool.hRhs i] at h
      exact h
    · exact False.elim (quotient_bound_exceeds_length (hLe i) D (hSource i) (by omega))
  apply hNoModel x
  apply rootHolds_from_label_bounds cfg.occSys x (activeSet := active)
  · exact occVectorIntPadded_nonneg classify pad
  · rw [hBool.hTarget]
    exact le_of_eq (occVectorIntPadded_total classify pad hrt).symm
  · exact hbound
  · intro i j
    rw [hBool.hIndicator]
    simp [active]

end QiushiMatmul.FrozenRegistry

run_cmd do
  let name := ``QiushiMatmul.FrozenRegistry.padded_plane_qra
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless allowed.contains ax do
      throwError "Unexpected axiom {ax} in {name}"
  Lean.logInfo m!"PADDED_EXTRACTION_AXIOMS {axioms}"
#check QiushiMatmul.FrozenRegistry.padded_plane_qra
