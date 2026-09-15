import QiushiGlobalOrbitDuality

/-! A table closed under one-vector extensions covers every finite-dimensional subspace. -/
open Matrix
namespace QiushiMatmul.GlobalOrbit
open PlaneOrbit
attribute [local instance] Classical.propDecidable Fintype.ofFinite
noncomputable section

def extend (W : Space) (X : Mat3) : Space := W ⊔ Submodule.span F2 {X}

theorem gen_extend (g : Fin 4) (W : Space) (X : Mat3) :
    genW g (extend W X) = extend (genW g W) (genMap g X) := by
  simp only [extend, genW, Submodule.map_sup, Submodule.map_span, Set.image_singleton]

def ExtensionStable (W : Space) : Prop := ∀ X : Mat3, Covered (extend W X)

theorem extensionStable_closed : GeneratorClosed {W | ExtensionStable W} := by
  intro g W hW X
  have h := covered_of_equivalent (hW (genMap g X))
    (generator_equivalent g (extend W (genMap g X)))
  simpa only [gen_extend, genMap_involution] using h

theorem extensionStable_of_equivalent {W V : Space} (hW : ExtensionStable W)
    (h : Equivalent W V) : ExtensionStable V :=
  (equivalent_mem_iff extensionStable_closed h).mp hW

theorem spanCodes_cons (c : Nat) (bs : List Nat) :
    spanCodes (c :: bs) = extend (spanCodes bs) (codeMat c) := by
  unfold spanCodes extend
  rw [← Submodule.span_union]
  congr 1
  ext X
  simp only [Set.mem_ofPred_eq, List.mem_cons, Set.mem_union, Set.mem_singleton_iff]
  aesop

def ExtensionChecks : Prop :=
  ∀ i : Fin 496, ∀ c : Fin 512, Covered (spanCodes (c.val :: frozenWangBasis i))

theorem representative_extension_stable (h : ExtensionChecks) (i : Fin 496) :
    ExtensionStable (representative i) := by
  intro X
  have hi := h i (matrixCode X)
  have hx : codeMat (matrixCode X).val = X := codeMat_matrixCode X
  rw [spanCodes_cons, hx] at hi
  exact hi

theorem covered_extension (h : ExtensionChecks) {W : Space} (hW : Covered W) (X : Mat3) :
    Covered (extend W X) := by
  obtain ⟨i, hi⟩ := hW
  exact extensionStable_of_equivalent (representative_extension_stable h i)
    ((frozen_image_iff i W).mp hi) X

theorem zero_covered : Covered (⊥ : Space) := by
  refine ⟨495, (frozen_image_iff 495 _).mpr ?_⟩
  have he : representative 495 = ⊥ := by
    change spanCodes [] = ⊥
    simp [spanCodes]
  rw [he]
  exact equivalent_refl _

/-- At most 496*512 semantic transition checks suffice; orbit expansions are unnecessary. -/
theorem coverage_of_extensions (h : ExtensionChecks) : ∀ W : Space, Covered W := by
  have hs : ∀ s : Finset Mat3, Covered (Submodule.span F2 (s : Set Mat3)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using zero_covered
    | @insert X s hX ih =>
      have he : Submodule.span F2 ((insert X s : Finset Mat3) : Set Mat3) =
          extend (Submodule.span F2 (s : Set Mat3)) X := by
        simp only [Finset.coe_insert, Submodule.span_insert, extend, sup_comm]
      rw [he]
      exact covered_extension h ih X
  intro W
  let s : Finset Mat3 := Finset.univ.filter (fun X => X ∈ W)
  have he : (s : Set Mat3) = (W : Set Mat3) := by ext X; simp [s]
  simpa only [he, Submodule.span_eq] using hs s

theorem global_coverage_iff_extensions : (∀ W : Space, Covered W) ↔ ExtensionChecks :=
  ⟨fun h _ _ => h _, coverage_of_extensions⟩

end
end QiushiMatmul.GlobalOrbit
