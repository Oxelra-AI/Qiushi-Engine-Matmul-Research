import QiushiPlaneOrbit484
import QiushiPlaneOrbit485
import QiushiPlaneOrbit486
import QiushiPlaneOrbit487
import QiushiPlaneOrbit488
import QiushiPlaneOrbit489
import QiushiPlaneOrbit490
import QiushiPlaneOrbit491

/-! Exact sizes and inequivalence for the eight representatives in report Table dim2.
This module neither counts all planes nor claims the full fourteen-orbit classification. -/

namespace QiushiMatmul.PlaneOrbit
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

def reportedSize (i : Fin 8) : Nat := ![98, 2352, 1176, 3528, 14112, 4704, 4704, 1344] i

def certificate (i : Fin 8) : Σ n, OrbitData n :=
  match i.val with
  | 0 => ⟨97, Orbit484.data⟩
  | 1 => ⟨2351, Orbit485.data⟩
  | 2 => ⟨1175, Orbit486.data⟩
  | 3 => ⟨3527, Orbit487.data⟩
  | 4 => ⟨14111, Orbit488.data⟩
  | 5 => ⟨4703, Orbit489.data⟩
  | 6 => ⟨4703, Orbit490.data⟩
  | _ => ⟨1343, Orbit491.data⟩

theorem certificate_checked (i : Fin 8) : ∀ j, (certificate i).2.RowOK j := by
  fin_cases i
  · exact Orbit484.checked
  · exact Orbit485.checked
  · exact Orbit486.checked
  · exact Orbit487.checked
  · exact Orbit488.checked
  · exact Orbit489.checked
  · exact Orbit490.checked
  · exact Orbit491.checked

theorem certificate_root (i : Fin 8) : (certificate i).2.space 0 = ahPlaneW i := by
  have swap (a b : Nat) : plane a b = plane b a := by
    unfold plane
    rw [Set.pair_comm]
  fin_cases i
  · exact swap 10 19
  · exact swap 10 20
  · exact swap 10 68
  · exact swap 10 84
  · exact swap 10 96
  · exact swap 10 258
  · exact swap 10 275
  · exact swap 84 163

theorem certificate_size (i : Fin 8) : (certificate i).1 + 1 = reportedSize i := by
  fin_cases i <;> rfl

theorem representative_dimension (i : Fin 8) : Module.finrank F2 (ahPlaneW i) = 2 := by
  rw [← certificate_root]
  exact (certificate i).2.dimension (certificate_checked i) 0

/-- Counts actual submodules in the full invertible-action/transpose orbit, not bases. -/
theorem exact_orbit_sizes (i : Fin 8) :
    Nat.card {W : Submodule F2 Mat3 // Equivalent (ahPlaneW i) W} = reportedSize i := by
  rw [← certificate_root]
  exact ((certificate i).2.orbit_card (certificate_checked i)).trans (certificate_size i)

def representativeKey (i : Fin 8) : Nat := ![5139, 5140, 5188, 5204, 5216, 5378, 5395, 43171] i

theorem certificate_key (i : Fin 8) : (certificate i).2.key 0 = representativeKey i := by
  fin_cases i <;> rfl

theorem representativeKey_injective : Function.Injective representativeKey := by
  decide +revert

/-- Includes the equal-sized, but inequivalent, orbits 489 and 490. -/
theorem representatives_inequivalent (i j : Fin 8) (hij : i ≠ j) :
    ¬ Equivalent (ahPlaneW i) (ahPlaneW j) := by
  intro h
  rw [← certificate_root i, ← certificate_root j] at h
  have hk := (certificate i).2.equivalent_root_keys (certificate_checked i)
    (certificate j).2 (certificate_checked j) h
  rw [certificate_key, certificate_key] at hk
  exact hij (representativeKey_injective hk)

theorem orbit_member_dimension (i : Fin 8) (W : Submodule F2 Mat3)
    (h : Equivalent (ahPlaneW i) W) : Module.finrank F2 W = 2 := by
  rw [← certificate_root] at h
  obtain ⟨j, rfl⟩ := ((certificate i).2.orbit_exact (certificate_checked i) W).mp h
  exact (certificate i).2.dimension (certificate_checked i) j

theorem no_invertible_transport (i j : Fin 8) (hij : i ≠ j)
    (P Q : Mat3) (hP : IsUnit P.det) (hQ : IsUnit Q.det) (tr : Bool) :
    actionW P Q (if tr then transposeW (ahPlaneW i) else ahPlaneW i) ≠ ahPlaneW j := by
  intro he
  apply representatives_inequivalent i j hij
  have ht : Equivalent (ahPlaneW i)
      (if tr then transposeW (ahPlaneW i) else ahPlaneW i) := by
    cases tr
    · exact equivalent_refl _
    · exact transpose_equivalent _
  rw [← he]
  exact equivalent_trans ht (action_equivalent _ P Q hP hQ)

theorem distinct_orbits_disjoint (i j : Fin 8) (hij : i ≠ j) :
    Disjoint {W : Submodule F2 Mat3 | Equivalent (ahPlaneW i) W}
      {W : Submodule F2 Mat3 | Equivalent (ahPlaneW j) W} := by
  rw [Set.disjoint_left]
  intro W hi hj
  exact representatives_inequivalent i j hij (equivalent_trans hi (equivalent_symm hj))

def orbitSetoid : Setoid Space := Relation.EqvGen.setoid ActionStep

def representedOrbits : Set (Quotient orbitSetoid) :=
  Set.range (fun i : Fin 8 => (⟦ahPlaneW i⟧ : Quotient orbitSetoid))

/-- Eight distinct quotient classes represented by this table, not a claim about all planes. -/
theorem represented_orbit_count : Nat.card representedOrbits = 8 := by
  have hinj : Function.Injective (fun i : Fin 8 => (⟦ahPlaneW i⟧ : Quotient orbitSetoid)) := by
    intro i j he
    by_contra hij
    exact representatives_inequivalent i j hij (Quotient.exact he)
  unfold representedOrbits
  rw [← Nat.card_congr (Equiv.ofInjective _ hinj), Nat.card_fin]

end QiushiMatmul.PlaneOrbit
