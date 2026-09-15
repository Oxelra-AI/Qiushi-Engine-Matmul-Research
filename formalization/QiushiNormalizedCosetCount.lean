import QiushiE11SubspaceCount
import QiushiCodeSpanBridgeCore

/-!
# The fifteen hyperplanes of the normalized coset span

Counts refer to actual submodules of the report's coded matrix space.
The named first-row family and fourteen affine hyperplanes form the full list;
no numerical quotient-rank labels are used.
-/

open Matrix BigOperators

namespace QiushiMatmul.NormalizedCosetCount

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private def spanFrame : Fin 4 → Mat3 :=
  ![codeMat 272, codeMat 4, codeMat 2, codeMat 1]

private theorem spanFrame_independent : LinearIndependent F2 spanFrame := by
  rw [Fintype.linearIndependent_iff]
  decide

private theorem spanFrame_span :
    Submodule.span F2 (Set.range spanFrame) = normalizedCosetSpan := by
  congr 1
  ext M
  simp [spanFrame, or_comm, or_assoc]

theorem normalizedCosetSpan_finrank : Module.finrank F2 normalizedCosetSpan = 4 := by
  rw [← spanFrame_span]
  simpa using finrank_span_eq_card spanFrame_independent

/-- The report's actual subspaces, with the first-row family at index zero. -/
def reportHyperplane : Fin 15 → Submodule F2 Mat3 :=
  Fin.cases firstRowFamily affineHyperplane

private def frameCodes : Fin 15 → Fin 3 → Nat :=
  ![![4,2,1], ![272,4,2], ![273,4,2], ![272,4,1], ![274,4,1],
    ![272,4,3], ![273,4,3], ![272,2,1], ![276,2,1], ![272,5,2],
    ![273,5,2], ![272,6,1], ![274,6,1], ![272,5,3], ![273,5,3]]

private def hyperplaneFrame (i : Fin 15) (j : Fin 3) : Mat3 := codeMat (frameCodes i j)

private theorem hyperplaneFrame_span (i : Fin 15) :
    Submodule.span F2 (Set.range (hyperplaneFrame i)) = reportHyperplane i := by
  fin_cases i <;>
    (congr 1
     ext M
     simp [hyperplaneFrame, frameCodes, Set.mem_range, Fin.exists_fin_succ, eq_comm])

private theorem hyperplaneFrame_independent (i : Fin 15) :
    LinearIndependent F2 (hyperplaneFrame i) := by
  have h : ∀ i : Fin 15, ∀ g : Fin 3 → F2,
      ∑ j, g j • hyperplaneFrame i j = 0 → ∀ j, g j = 0 := by decide
  exact Fintype.linearIndependent_iff.mpr (h i)

theorem reportHyperplane_finrank (i : Fin 15) :
    Module.finrank F2 (reportHyperplane i) = 3 := by
  rw [← hyperplaneFrame_span]
  simpa using finrank_span_eq_card (hyperplaneFrame_independent i)

theorem reportHyperplane_le (i : Fin 15) : reportHyperplane i ≤ normalizedCosetSpan := by
  rw [← hyperplaneFrame_span]
  apply Submodule.span_le.mpr
  rintro M ⟨j, rfl⟩
  have h : ∀ (i : Fin 15) (j : Fin 3),
      spanContainsCode [272,4,2,1] (frameCodes i j) = true := by decide
  exact spanContainsCode_implies_mem_spanCodes _ _ (h i j)

private def pivot : Fin 4 → Coord9 := ![(1,1), (0,2), (0,1), (0,0)]

private def entryEval (c : Coord9) : Mat3 →ₗ[F2] F2 where
  toFun M := M c.1 c.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def normalCode : Fin 15 → Nat := ![1,8,9,4,5,12,13,2,3,10,11,6,7,14,15]

private def normal (i : Fin 15) : Mat3 →ₗ[F2] F2 :=
  ∑ j : Fin 4, (if Nat.testBit (normalCode i) j.val then (1 : F2) else 0) • entryEval (pivot j)

private theorem normal_kills :
    ∀ (i : Fin 15) (j : Fin 3), normal i (hyperplaneFrame i j) = 0 := by decide

private theorem normal_distinguishes :
    ∀ (i j : Fin 15), i ≠ j → ∃ k : Fin 3, normal j (hyperplaneFrame i k) ≠ 0 := by
  decide

theorem reportHyperplane_injective : Function.Injective reportHyperplane := by
  intro i j hij
  by_contra hne
  obtain ⟨k, hk⟩ := normal_distinguishes i j hne
  have hker : reportHyperplane j ≤ LinearMap.ker (normal j) := by
    rw [← hyperplaneFrame_span]
    apply Submodule.span_le.mpr
    rintro M ⟨l, rfl⟩
    exact normal_kills j l
  apply hk
  apply hker
  rw [← hij, ← hyperplaneFrame_span]
  exact Submodule.subset_span (Set.mem_range_self k)

theorem firstRowFamily_finrank : Module.finrank F2 firstRowFamily = 3 :=
  reportHyperplane_finrank 0

/-- Three-dimensional subspaces contained in the actual four-dimensional span. -/
abbrev Hyperplanes :=
  {U : Submodule F2 Mat3 // U ≤ normalizedCosetSpan ∧ Module.finrank F2 U = 3}

noncomputable section

open E11SubspaceCount
attribute [local instance] Fintype.ofFinite

private def hyperplanesEquiv : Hyperplanes ≃ Spaces normalizedCosetSpan 3 where
  toFun U := ⟨U.val.comap normalizedCosetSpan.subtype,
    (Submodule.comapSubtypeEquivOfLe U.property.1).finrank_eq.trans U.property.2⟩
  invFun P := ⟨P.val.map normalizedCosetSpan.subtype, by
    constructor
    · exact Submodule.map_le_iff_le_comap.mpr (fun x _ => x.property)
    · rw [Submodule.finrank_map_subtype_eq, P.property]⟩
  left_inv U := by
    apply Subtype.ext
    change (U.val.comap normalizedCosetSpan.subtype).map normalizedCosetSpan.subtype = U.val
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr U.property.1]
  right_inv P := by
    apply Subtype.ext
    exact Submodule.comap_map_eq_of_injective normalizedCosetSpan.injective_subtype P.val

theorem normalizedCosetSpan_hyperplane_count : Nat.card Hyperplanes = 15 := by
  have h := subspace_count_mul_frameCount normalizedCosetSpan (k := 3)
    (by rw [normalizedCosetSpan_finrank]; omega)
  rw [normalizedCosetSpan_finrank] at h
  norm_num [frameCount, Fin.prod_univ_succ] at h
  rw [Nat.card_congr hyperplanesEquiv, Nat.card_eq_fintype_card]
  omega

private def namedHyperplane (i : Fin 15) : Hyperplanes :=
  ⟨reportHyperplane i, reportHyperplane_le i, reportHyperplane_finrank i⟩

private theorem namedHyperplane_bijective : Function.Bijective namedHyperplane := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro i j h
    exact reportHyperplane_injective (congrArg Subtype.val h)
  · simpa using normalizedCosetSpan_hyperplane_count.symm

/-- Completeness and uniqueness refer to the named subspaces, not a count-only index. -/
theorem report_hyperplane_complete (U : Submodule F2 Mat3)
    (hU : U ≤ normalizedCosetSpan) (hd : Module.finrank F2 U = 3) :
    ∃! i : Fin 15, reportHyperplane i = U := by
  obtain ⟨i, hi⟩ := namedHyperplane_bijective.surjective ⟨U,hU,hd⟩
  refine ⟨i, congrArg Subtype.val hi, ?_⟩
  intro j hj
  exact reportHyperplane_injective (hj.trans (congrArg Subtype.val hi).symm)

/-- Exactly the fourteen hyperplanes other than the first-row family. -/
abbrev AffineHyperplanes :=
  {U : Submodule F2 Mat3 // U ≤ normalizedCosetSpan ∧
    Module.finrank F2 U = 3 ∧ U ≠ firstRowFamily}

def affineHyperplanesEquiv : Fin 14 ≃ AffineHyperplanes :=
  Equiv.ofBijective
    (fun i => ⟨affineHyperplane i, reportHyperplane_le i.succ,
      reportHyperplane_finrank i.succ, fun h =>
        Fin.succ_ne_zero i (reportHyperplane_injective (show reportHyperplane i.succ =
          reportHyperplane 0 from h))⟩)
    (by
      constructor
      · intro i j h
        exact Fin.succ_injective _ (reportHyperplane_injective (congrArg Subtype.val h))
      · intro U
        obtain ⟨i, hi, _⟩ := report_hyperplane_complete U.val U.property.1 U.property.2.1
        refine Fin.cases ?_ (fun j hj => ?_) i hi
        · intro h
          exact (U.property.2.2 h.symm).elim
        · exact ⟨j, Subtype.ext hj⟩)

theorem affine_hyperplane_count : Nat.card AffineHyperplanes = 14 := by
  rw [← Nat.card_congr affineHyperplanesEquiv]
  simp

theorem affine_hyperplane_complete (U : Submodule F2 Mat3)
    (hU : U ≤ normalizedCosetSpan) (hd : Module.finrank F2 U = 3)
    (hne : U ≠ firstRowFamily) : ∃! i : Fin 14, affineHyperplane i = U := by
  let u : AffineHyperplanes := ⟨U,hU,hd,hne⟩
  refine ⟨affineHyperplanesEquiv.symm u,
    congrArg Subtype.val (affineHyperplanesEquiv.apply_symm_apply u), ?_⟩
  intro i hi
  apply affineHyperplanesEquiv.injective
  rw [affineHyperplanesEquiv.apply_symm_apply]
  exact Subtype.ext hi

end
end QiushiMatmul.NormalizedCosetCount
