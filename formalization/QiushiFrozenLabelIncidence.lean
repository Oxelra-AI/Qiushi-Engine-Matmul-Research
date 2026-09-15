import QiushiFrozenLabelPointProfile
import QiushiPlaneOrbitFrozenClassification

namespace QiushiMatmul.FrozenLabel

open FrozenL0Report PlaneOrbit PlaneOrbit.FullClassification

noncomputable def containedCount (root W : Space) : Nat :=
  Nat.card {U : Space // Equivalent root U ∧ U ≤ W}

theorem containedCount_gen (root W : Space) (g : Fin 4) :
    containedCount root (genW g W) = containedCount root W := by
  let e : Space ≃ Space :=
    { toFun := genW g
      invFun := genW g
      left_inv := genW_involution g
      right_inv := genW_involution g }
  apply Eq.symm
  apply Nat.card_congr (e.subtypeEquiv (p := fun U : Space => _)
    (q := fun U : Space => _) ?_)
  intro U
  change (Equivalent root U ∧ U ≤ W) ↔
    (Equivalent root (genW g U) ∧ genW g U ≤ genW g W)
  have he : Equivalent root U ↔ Equivalent root (genW g U) :=
    ⟨fun h => equivalent_trans h (generator_equivalent g U),
     fun h => equivalent_trans h (equivalent_symm (generator_equivalent g U))⟩
  rw [he, genW, genW,
    Submodule.map_le_map_iff_of_injective
      (Function.Involutive.injective (genMap_involution g))]

theorem containedCount_equivalent (root : Space) {W V : Space} (h : Equivalent W V) :
    containedCount root W = containedCount root V := by
  let S : Set Space := {U | containedCount root U = containedCount root W}
  have hS : GeneratorClosed S := by
    intro g U hU
    exact (containedCount_gen root U g).trans hU
  exact ((equivalent_mem_iff hS h).mp rfl).symm

def codeContainedCount {n : Nat} (D : OrbitData n) (bs : List Nat) : Nat :=
  (Finset.univ.filter fun i =>
    clampCode (D.row i).a ∈ spanEnum bs ∧ clampCode (D.row i).b ∈ spanEnum bs).card

theorem plane_le_spanCodes (a b : Nat) (bs : List Nat) :
    plane a b ≤ spanCodes bs ↔
      clampCode a ∈ spanEnum bs ∧ clampCode b ∈ spanEnum bs := by
  rw [mem_spanEnum, mem_spanEnum]
  change plane a b ≤ spanCodes bs ↔
    codeMat (a &&& 511) ∈ spanCodes bs ∧ codeMat (b &&& 511) ∈ spanCodes bs
  rw [codeMat_and_511, codeMat_and_511, plane, Submodule.span_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]

theorem codeContainedCount_correct {n : Nat} (D : OrbitData n)
    (hD : ∀ i, D.RowOK i) (bs : List Nat) :
    codeContainedCount D bs = containedCount (D.space 0) (spanCodes bs) := by
  classical
  let e : {i // i ∈ (Finset.univ : Finset (Fin (n + 1)))} ≃ Fin (n + 1) :=
    { toFun := Subtype.val
      invFun := fun i => ⟨i, Finset.mem_univ i⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := filter_card_eq_natCard Finset.univ
    (e.trans (D.orbitEquiv hD))
    (fun i => clampCode (D.row i).a ∈ spanEnum bs ∧ clampCode (D.row i).b ∈ spanEnum bs)
    (fun U : {U : Space // Equivalent (D.space 0) U} => U.val ≤ spanCodes bs)
    (fun i => by
      change (_ ∧ _) ↔ plane (D.row i.val).a (D.row i.val).b ≤ spanCodes bs
      exact (plane_le_spanCodes (D.row i.val).a (D.row i.val).b bs).symm)
  exact h.trans (Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (Equivalent (D.space 0)) (fun U => U ≤ spanCodes bs)))

def planeIncidence (k : Fin 14) (bs : List Nat) : Nat :=
  codeContainedCount (family k).2 bs

theorem planeIncidence_correct (k : Fin 14) (bs : List Nat) :
    planeIncidence k bs = containedCount (frozenRep k) (spanCodes bs) := by
  rw [planeIncidence, codeContainedCount_correct _ (family_checked k), family_root]

theorem planeIncidence_eq_of_overlap (k : Fin 14) (i j : Fin 496) (W : Space)
    (hi : frozenWangTable.OrbitImage i W) (hj : frozenWangTable.OrbitImage j W) :
    planeIncidence k (frozenWangBasis i) = planeIncidence k (frozenWangBasis j) := by
  rw [planeIncidence_correct, planeIncidence_correct]
  exact containedCount_equivalent _ (equivalent_trans
    ((orbit_image_iff_equivalent i W).mp hi)
    (equivalent_symm ((orbit_image_iff_equivalent j W).mp hj)))

end QiushiMatmul.FrozenLabel
