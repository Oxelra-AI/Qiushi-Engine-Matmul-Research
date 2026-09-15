import QiushiPlaneOrbitSizes
import QiushiPlaneOrbit478
import QiushiPlaneOrbit479
import QiushiPlaneOrbit480
import QiushiPlaneOrbit481
import QiushiPlaneOrbit482
import QiushiPlaneOrbit483
import QiushiFrozenWangData
import QiushiMat3SubspaceCount

/-! Independent report classification. Coverage follows from the existing count of
actual two-dimensional submodules and the disjoint, exact orbit certificates. -/

open BigOperators
namespace QiushiMatmul.PlaneOrbit.FullClassification
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable Fintype.ofFinite
noncomputable section

def family (i : Fin 14) : Σ n, OrbitData n :=
  match i.val with
  | 0 => ⟨97, Orbit478.data⟩
  | 1 => ⟨440, Orbit479.data⟩
  | 2 => ⟨881, Orbit480.data⟩
  | 3 => ⟨3527, Orbit481.data⟩
  | 4 => ⟨1763, Orbit482.data⟩
  | 5 => ⟨4703, Orbit483.data⟩
  | _ => certificate ⟨i.val - 6, by omega⟩

theorem family_checked (i : Fin 14) : ∀ j, (family i).2.RowOK j := by
  fin_cases i
  · exact Orbit478.checked
  · exact Orbit479.checked
  · exact Orbit480.checked
  · exact Orbit481.checked
  · exact Orbit482.checked
  · exact Orbit483.checked
  · exact certificate_checked 0
  · exact certificate_checked 1
  · exact certificate_checked 2
  · exact certificate_checked 3
  · exact certificate_checked 4
  · exact certificate_checked 5
  · exact certificate_checked 6
  · exact certificate_checked 7

def frozenRep (i : Fin 14) : Space :=
  spanCodes (frozenWangBasis ⟨478 + i.val, by omega⟩)

theorem family_root (i : Fin 14) : (family i).2.space 0 = frozenRep i := by
  have swap (a b : Nat) : plane a b = spanCodes [b, a] := by
    rw [ah_spanCodes_pair]
    unfold plane
    rw [Set.pair_comm]
  fin_cases i
  · exact swap 1 2
  · exact swap 1 10
  · exact swap 1 16
  · exact swap 1 20
  · exact swap 1 84
  · exact swap 1 160
  · exact swap 10 19
  · exact swap 10 20
  · exact swap 10 68
  · exact swap 10 84
  · exact swap 10 96
  · exact swap 10 258
  · exact swap 10 275
  · exact swap 84 163

def sizes : Fin 14 → Nat :=
  ![98, 441, 882, 3528, 1764, 4704, 98, 2352, 1176, 3528, 14112, 4704, 4704, 1344]

theorem family_size (i : Fin 14) : (family i).1 + 1 = sizes i := by
  fin_cases i <;> rfl

theorem representative_dimension (i : Fin 14) : Module.finrank F2 (frozenRep i) = 2 := by
  rw [← family_root]
  exact (family i).2.dimension (family_checked i) 0

theorem exact_orbit_sizes (i : Fin 14) :
    Nat.card {W : Space // Equivalent (frozenRep i) W} = sizes i := by
  rw [← family_root]
  exact ((family i).2.orbit_card (family_checked i)).trans (family_size i)

private def rootKey : Fin 14 → Nat :=
  ![514, 522, 528, 532, 596, 672, 5139, 5140, 5188, 5204, 5216, 5378, 5395, 43171]

private theorem family_key (i : Fin 14) : (family i).2.key 0 = rootKey i := by
  fin_cases i <;> rfl

private theorem rootKey_injective : Function.Injective rootKey := by
  decide +kernel +revert

theorem representatives_inequivalent (i j : Fin 14) (hij : i ≠ j) :
    ¬ Equivalent (frozenRep i) (frozenRep j) := by
  intro h
  rw [← family_root i, ← family_root j] at h
  have hk := (family i).2.equivalent_root_keys (family_checked i)
    (family j).2 (family_checked j) h
  rw [family_key, family_key] at hk
  exact hij (rootKey_injective hk)

abbrev Points := Σ i : Fin 14, Fin ((family i).1 + 1)
abbrev Planes := {W : Space // Module.finrank F2 W = 2}

def toPlane (p : Points) : Planes :=
  ⟨(family p.1).2.space p.2, (family p.1).2.dimension (family_checked p.1) p.2⟩

theorem toPlane_injective : Function.Injective toPlane := by
  rintro ⟨i, a⟩ ⟨j, b⟩ he
  have hw : (family i).2.space a = (family j).2.space b := congrArg Subtype.val he
  have hi := (family i).2.connected (family_checked i) a
  have hj := (family j).2.connected (family_checked j) b
  rw [family_root, hw] at hi
  rw [family_root] at hj
  have hij : i = j := by
    by_contra hn
    exact representatives_inequivalent i j hn (equivalent_trans hi (equivalent_symm hj))
  subst j
  have hab := (family i).2.space_injective (family_checked i) hw
  subst b
  rfl

theorem points_card : Nat.card Points = 43435 := by
  rw [Points, Nat.card_sigma]
  simp_rw [Nat.card_fin, family_size]
  norm_num [sizes, Fin.sum_univ_succ]

theorem toPlane_bijective : Function.Bijective toPlane := by
  apply (Fintype.bijective_iff_injective_and_card toPlane).mpr
  refine ⟨toPlane_injective, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, points_card]
  exact FullSubspaceCount.mat3_two_plane_count.symm

/-- No exhaustive classifier is used: an injection of 43435 certified planes is onto. -/
theorem classification (W : Space) (hW : Module.finrank F2 W = 2) :
    ∃! i : Fin 14, Equivalent (frozenRep i) W := by
  obtain ⟨⟨i, a⟩, he⟩ := toPlane_bijective.2 ⟨W, hW⟩
  have hw : (family i).2.space a = W := congrArg Subtype.val he
  have hi := (family i).2.connected (family_checked i) a
  rw [family_root, hw] at hi
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  exact representatives_inequivalent j i hji (equivalent_trans hj (equivalent_symm hi))

def twoPlaneOrbits : Set (Quotient orbitSetoid) :=
  {q | ∃ W : Space, Module.finrank F2 W = 2 ∧ (⟦W⟧ : Quotient orbitSetoid) = q}

def toOrbit (i : Fin 14) : twoPlaneOrbits :=
  ⟨⟦frozenRep i⟧, ⟨frozenRep i, representative_dimension i, rfl⟩⟩

theorem toOrbit_bijective : Function.Bijective toOrbit := by
  constructor
  · intro i j he
    by_contra hij
    exact representatives_inequivalent i j hij (Quotient.exact (congrArg Subtype.val he))
  · rintro ⟨q, W, hW, rfl⟩
    obtain ⟨i, hi, _⟩ := classification W hW
    exact ⟨i, Subtype.ext (Quotient.sound hi)⟩

/-- Exactly fourteen full-action equivalence classes of actual two-dimensional submodules. -/
theorem orbit_count : Nat.card twoPlaneOrbits = 14 := by
  rw [← Nat.card_congr (Equiv.ofBijective toOrbit toOrbit_bijective), Nat.card_fin]

end
end QiushiMatmul.PlaneOrbit.FullClassification
