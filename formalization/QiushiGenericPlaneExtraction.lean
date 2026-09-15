import QiushiExtractionBridgePadded
import QiushiExtractionBridge
import QiushiOccupationAPI
import QiushiOccupation
import QiushiCodeSpanBridgeCore
import QiushiOccupationSoundness
import QiushiOccBranchBridge
import QiushiLineOrbit

/-!
# Generic plane extraction theorem

One parametric theorem for all-high planes and line planes, proving
`QuotientRankAtLeast W (target + 1)` from:

1. **`PlaneExtConfig`**: pure Nat-code data (bases, labels, sections, OccSys)
2. **Source `QuotientRankAtLeast`** facts from the theorem ledger or residual structure
3. **Dead-witness `QuotientRankAtLeast`** facts at exactly `target`
4. **`PlaneExtBool`**: Boolean facts proved by `decide +revert` on 9-bit codes
5. **No-model certificate**: `∀ x, OccSys.RootHolds occSys x → False`

Each plane instantiation contains ONLY tables, decide shards, and applications of
ledger or residual theorems. No Finset or Submodule reasoning.

## Mathematical mechanism

For r < target: `quotient_bound_exceeds_length` from any dead witness kills the
decomposition.

For r = target: `occupation_inequality` on each dead witness gives kill-count ≤ 0.
Every code classified as dead/zero is in some dead witness (hDeadCover), so its
entire fiber is in the killSet; emptiness follows. The live total = r = target
exactly. Source occupation rows bound the live fiber vector. The no-model
certificate contradicts the existence of such a vector.

No padding arithmetic: dead witnesses at target level force x₀ = 0 and all dead
fibers empty, so the live restriction is exact.
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

open BigOperators Finset Matrix

namespace QiushiMatmul

/-- Pure data configuration for a plane extraction instance. -/
structure PlaneExtConfig where
  /-- Number of occupation rows (= number of source subspaces) -/
  nOcc : Nat
  /-- Number of dead-witness subspaces (must be > 0) -/
  nDead : Nat
  /-- Number of live quotient labels -/
  nLive : Nat
  /-- Target: proving QuotientRankAtLeast W (target + 1) -/
  target : Nat
  /-- Plane basis: list of 9-bit matrix codes -/
  planeBasis : List Nat
  /-- Source basis for each occupation row -/
  sourceBasis : Fin nOcc → List Nat
  /-- Source lower bound for each occupation row -/
  sourceLb : Fin nOcc → Nat
  /-- Dead-witness basis for each dead witness -/
  deadBasis : Fin nDead → List Nat
  /-- Classification: maps each 9-bit code to Fin (nLive + 1).
      Value 0 = "dead or zero" (killed by dead witnesses).
      Value j+1 = "live label j" (contributes to occupation system). -/
  classifyCode : Fin 512 → Fin (nLive + 1)
  /-- Section representative code for each live label -/
  sectionCode : Fin nLive → Fin 512
  /-- Dead-witness assignment for each dead/zero code.
      Only used when classifyCode c = 0; arbitrary otherwise. -/
  deadCover : Fin 512 → Fin nDead
  /-- Occupation system over live labels -/
  occSys : OccSys nLive nOcc

/-- The plane subspace. -/
abbrev PlaneExtConfig.W (cfg : PlaneExtConfig) : Submodule F2 Mat3 :=
  spanCodes cfg.planeBasis

/-- Source subspace for occupation row i. -/
abbrev PlaneExtConfig.sourceU (cfg : PlaneExtConfig) (i : Fin cfg.nOcc) : Submodule F2 Mat3 :=
  spanCodes (cfg.sourceBasis i)

/-- Dead-witness subspace for dead index d. -/
abbrev PlaneExtConfig.deadU (cfg : PlaneExtConfig) (d : Fin cfg.nDead) : Submodule F2 Mat3 :=
  spanCodes (cfg.deadBasis d)

/-- Code-level Boolean facts for the plane extraction.
All fields are discharged by `decide +revert` in the instantiation. -/
structure PlaneExtBool (cfg : PlaneExtConfig) where
  /-- Section coset consistency: if classifyCode c = j+1, then
      c XOR sectionCode j is in spanCodes planeBasis (i.e., in W). -/
  hSectionCoset : ∀ (c : Fin 512) (j : Fin cfg.nLive),
    (cfg.classifyCode c).val = j.val + 1 →
    spanContainsCode cfg.planeBasis (c.val ^^^ (cfg.sectionCode j).val) = true
  /-- Dead cover: if classifyCode c = 0, then c is in deadU(deadCover c). -/
  hDeadCover : ∀ (c : Fin 512),
    (cfg.classifyCode c).val = 0 →
    spanContainsCode (cfg.deadBasis (cfg.deadCover c)) c.val = true
  /-- Plane ≤ each source. -/
  hPlaneLeSource : ∀ (i : Fin cfg.nOcc) (g : Nat),
    g ∈ cfg.planeBasis → spanContainsCode (cfg.sourceBasis i) g = true
  /-- Plane ≤ each dead witness. -/
  hPlaneLeDead : ∀ (d : Fin cfg.nDead) (g : Nat),
    g ∈ cfg.planeBasis → spanContainsCode (cfg.deadBasis d) g = true
  /-- Indicator: occupation coefficient matches semantic section containment. -/
  hIndicator : ∀ (i : Fin cfg.nOcc) (j : Fin cfg.nLive),
    cfg.occSys.occCoeff i j =
      if spanContainsCode (cfg.sourceBasis i) (cfg.sectionCode j).val then 1 else 0
  /-- RHS: occupation system RHS = target − sourceLb. -/
  hRhs : ∀ (i : Fin cfg.nOcc),
    cfg.occSys.occRhs i = (cfg.target : Int) - (cfg.sourceLb i : Int)
  /-- OccSys target matches config target. -/
  hTarget : cfg.occSys.target = (cfg.target : Int)

-- ============================================================================
-- Helper lemmas: Boolean → Submodule, used once in the generic proof
-- ============================================================================

/-- Plane ≤ source from Boolean containment of generators. -/
theorem planeLeSource_of_bool {cfg : PlaneExtConfig} {i : Fin cfg.nOcc}
    (hGen : ∀ (g : Nat), g ∈ cfg.planeBasis →
      spanContainsCode (cfg.sourceBasis i) g = true)
    : cfg.W ≤ cfg.sourceU i := by
  unfold PlaneExtConfig.W PlaneExtConfig.sourceU spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM; rcases hM with ⟨n, hn, rfl⟩
    exact spanContainsCode_implies_mem_spanCodes (cfg.sourceBasis i) n (hGen n hn))

/-- Plane ≤ dead witness from Boolean containment of generators. -/
theorem planeLeDead_of_bool {cfg : PlaneExtConfig} {d : Fin cfg.nDead}
    (hGen : ∀ (g : Nat), g ∈ cfg.planeBasis →
      spanContainsCode (cfg.deadBasis d) g = true)
    : cfg.W ≤ cfg.deadU d := by
  unfold PlaneExtConfig.W PlaneExtConfig.deadU spanCodes
  exact Submodule.span_le.mpr (by
    intro M hM; rcases hM with ⟨n, hn, rfl⟩
    exact spanContainsCode_implies_mem_spanCodes (cfg.deadBasis d) n (hGen n hn))

-- ============================================================================
-- Main theorem
-- ============================================================================

/-- The generic plane extraction theorem.

Given a PlaneExtConfig with dead witnesses at target level, source QRA
bounds, Boolean code-level facts, and a no-model certificate,
proves `QuotientRankAtLeast W (target + 1)`.

All Finset and Submodule reasoning lives here. Plane instantiations provide
only Boolean tables and QuotientRankAtLeast theorem applications.
-/
theorem generic_plane_qra
    (cfg : PlaneExtConfig)
    (hBool : PlaneExtBool cfg)
    (hSourceQRA : ∀ i : Fin cfg.nOcc,
      QuotientRankAtLeast (cfg.sourceU i) (cfg.sourceLb i))
    (hDeadQRA : ∀ d : Fin cfg.nDead,
      QuotientRankAtLeast (cfg.deadU d) cfg.target)
    (hDeadPos : 0 < cfg.nDead)
    (hNoModel : ∀ x : Fin cfg.nLive → Int,
      cfg.occSys.RootHolds x → False)
    : QuotientRankAtLeast cfg.W (cfg.target + 1) := by
  -- Derive submodule containments from Boolean facts.
  have hWLeS : ∀ i : Fin cfg.nOcc, cfg.W ≤ cfg.sourceU i := fun i =>
    planeLeSource_of_bool (fun g hg => hBool.hPlaneLeSource i g hg)
  have hWLeD : ∀ d : Fin cfg.nDead, cfg.W ≤ cfg.deadU d := fun d =>
    planeLeDead_of_bool (fun g hg => hBool.hPlaneLeDead d g hg)
  intro r hr
  by_cases hlt : r < cfg.target
  · -- Below target, any one dead-witness quotient bound is already impossible.
    have d0 : Fin cfg.nDead := ⟨0, hDeadPos⟩
    exact ⟨fun D => quotient_bound_exceeds_length (hWLeD d0) D (hDeadQRA d0) hlt⟩
  · have hr_eq : r = cfg.target := by omega
    subst hr_eq
    exact ⟨fun D => by
      -- Classify every A-factor by its canonical 9-bit code.
      let classify : Fin cfg.target → Fin (cfg.nLive + 1) :=
        fun t => cfg.classifyCode (matrixCode (D.A t))

      -- At length target, each dead witness has an empty kill set.
      have hKillZero : ∀ d : Fin cfg.nDead,
          (killSet D (cfg.deadU d)).card = 0 := by
        intro d
        have h := occupation_inequality (hWLeD d) D (hDeadQRA d)
          (Nat.le_refl cfg.target)
        simpa using h

      -- Every label-0 term lies in its assigned dead witness, hence cannot exist.
      have hZero : occFiberCard' classify 0 = 0 := by
        unfold occFiberCard'
        apply Finset.card_eq_zero.mpr
        ext t
        constructor
        · intro htClass
          have htClass' : classify t = 0 := by
            simpa using (Finset.mem_filter.mp htClass).2
          let c : Fin 512 := matrixCode (D.A t)
          let d : Fin cfg.nDead := cfg.deadCover c
          have hClassVal : (cfg.classifyCode c).val = 0 := by
            have h := congrArg Fin.val htClass'
            simpa [classify, c] using h
          have hCover := hBool.hDeadCover c hClassVal
          have hCodeMem := spanContainsCode_implies_mem_spanCodes
            (cfg.deadBasis d) c.val (by simpa [d] using hCover)
          have hDecode : codeMat c.val = D.A t := by
            simpa [c, matrixCode] using codeMat_matrixCode (D.A t)
          have hMem : D.A t ∈ cfg.deadU d := by
            rw [← hDecode]
            exact hCodeMem
          have htKill : t ∈ killSet D (cfg.deadU d) := by
            simpa [killSet] using hMem
          have hEmpty : killSet D (cfg.deadU d) = ∅ :=
            Finset.card_eq_zero.mp (hKillZero d)
          rw [hEmpty] at htKill
          exact htKill
        · simp

      let x : Fin cfg.nLive → Int :=
        occVectorInt classify cfg.nLive (Nat.le_refl _)
      let activeSet : Fin cfg.nOcc → Finset (Fin cfg.nLive) := fun i =>
        Finset.univ.filter (fun j =>
          spanContainsCode (cfg.sourceBasis i) (cfg.sectionCode j).val = true)

      -- With the zero fiber gone, the live fibers have exact total target.
      have hTotalEq : ∑ j : Fin cfg.nLive, x j = (cfg.target : Int) := by
        dsimp [x]
        exact occVectorInt_total_of_zero classify hZero

      -- A live fiber selected by row i is contained in sourceU i. Reconstruction
      -- gives A + section ∈ W, and both W and the section lie in sourceU i.
      have hContain : ∀ (i : Fin cfg.nOcc) (t : Fin cfg.target),
          classify t ∈ (activeSet i).image Fin.succ → D.A t ∈ cfg.sourceU i := by
        intro i t ht
        rcases Finset.mem_image.mp ht with ⟨j, hj, hjLabel⟩
        have hjActive :
            spanContainsCode (cfg.sourceBasis i) (cfg.sectionCode j).val = true := by
          exact (Finset.mem_filter.mp hj).2
        let c : Fin 512 := matrixCode (D.A t)
        have hClass : cfg.classifyCode c = Fin.succ j := by
          simpa [classify, c] using hjLabel.symm
        have hClassVal : (cfg.classifyCode c).val = j.val + 1 := by
          simpa using congrArg Fin.val hClass
        have hCosetBool := hBool.hSectionCoset c j hClassVal
        have hCosetW := spanContainsCode_implies_mem_spanCodes
          cfg.planeBasis (c.val ^^^ (cfg.sectionCode j).val) hCosetBool
        change codeMat (Nat.xor c.val (cfg.sectionCode j).val) ∈ cfg.W at hCosetW
        rw [codeMat_xor] at hCosetW
        have hCosetU := hWLeS i hCosetW
        have hSectionU := spanContainsCode_implies_mem_spanCodes
          (cfg.sourceBasis i) (cfg.sectionCode j).val hjActive
        have hSum := (cfg.sourceU i).add_mem hCosetU hSectionU
        have hDecode : codeMat c.val = D.A t := by
          simpa [c, matrixCode] using codeMat_matrixCode (D.A t)
        rw [hDecode, add_assoc, mat3_add_self_eq_zero, add_zero] at hSum
        exact hSum

      -- Convert each semantic active set to the corresponding OccSys row.
      have hBound : ∀ i : Fin cfg.nOcc,
          ∑ j ∈ activeSet i, x j ≤ cfg.occSys.occRhs i := by
        intro i
        by_cases hLb : cfg.sourceLb i ≤ cfg.target
        · have h := live_labeled_fiber_occ_row_int (hWLeS i) D classify
            (activeSet i) (hContain i) (hSourceQRA i) hLb
            (Nat.le_refl cfg.target)
          have hCast : ((cfg.target - cfg.sourceLb i : Nat) : Int) =
              (cfg.target : Int) - (cfg.sourceLb i : Int) := by
            omega
          rw [hCast, ← hBool.hRhs i] at h
          exact h
        · have hLt : cfg.target < cfg.sourceLb i := by omega
          exact False.elim
            (quotient_bound_exceeds_length (hWLeS i) D (hSourceQRA i) hLt)

      apply hNoModel x
      apply rootHolds_from_label_bounds cfg.occSys x (activeSet := activeSet)
      · intro j
        dsimp [x]
        exact occVectorInt_nonneg classify (Nat.le_refl _) j
      · rw [hBool.hTarget, hTotalEq]
      · exact hBound
      · intro i j
        rw [hBool.hIndicator]
        simp [activeSet]
    ⟩

end QiushiMatmul
