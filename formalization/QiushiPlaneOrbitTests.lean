import QiushiPlaneOrbitSizes

open QiushiMatmul QiushiMatmul.PlaneOrbit

example : Nat.card {W : Submodule F2 Mat3 // Equivalent plane484 W} = 98 := by
  unfold plane484
  rw [ah_spanCodes_pair]
  exact exact_orbit_sizes 0

example : reportedSize 5 = reportedSize 6 := by decide
example : ¬ Equivalent (ahPlaneW 5) (ahPlaneW 6) := representatives_inequivalent 5 6 (by decide)

-- A closed self-loop alone is not an orbit certificate: this generator leaves the row.
def falseSingleton : OrbitData 0 :=
  ⟨fun _ => ⟨10, 19, 0, 0, 0, 0, 0, 0⟩⟩
example : ¬ falseSingleton.RowOK 0 := by decide

-- Noncanonical and dependent generators are rejected before any cardinality argument.
example : ¬ Valid 19 10 := by decide
example : ¬ Valid 10 10 := by decide
example : ¬ Valid 0 10 := by decide

#check exact_orbit_sizes
#check representatives_inequivalent
#check no_invertible_transport
#check represented_orbit_count
#check orbit_member_dimension
#print axioms QiushiMatmul.PlaneOrbit.genCode_semantics
#print axioms QiushiMatmul.PlaneOrbit.invertible_word
#print axioms QiushiMatmul.PlaneOrbit.OrbitData.orbit_exact
#print axioms QiushiMatmul.PlaneOrbit.exact_orbit_sizes
#print axioms QiushiMatmul.PlaneOrbit.representatives_inequivalent
#print axioms QiushiMatmul.PlaneOrbit.represented_orbit_count
