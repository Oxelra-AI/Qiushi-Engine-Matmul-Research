import QiushiFrozenLabelSmall

open QiushiMatmul QiushiMatmul.FrozenLabel QiushiMatmul.PlaneOrbit

example : LabelConsistent ↔ ∀ i : Fin 496,
    frozenWangTable.L0 (spanCodes (frozenWangBasis i)) = frozenWangLower i :=
  label_consistent_iff_exact_representatives

example (i : Fin 496) (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2))) :
    frozenWangTable.OrbitImage i W ↔ Equivalent (spanCodes (frozenWangBasis i)) W :=
  orbit_image_iff_equivalent i W

example (h : LabelConsistent) (i : Fin 496)
    (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hi : frozenWangTable.OrbitImage i W) : frozenWangTable.L0 W = frozenWangLower i :=
  exact_of_label_consistent h i hi

example (i : Fin 14) :
    frozenWangTable.L0 (spanCodes (frozenWangBasis ⟨478 + i.val, by omega⟩)) =
      frozenWangLower ⟨478 + i.val, by omega⟩ := plane_representative_exact i

example (i : Fin 496) (hi : 478 ≤ i.val) :
    frozenWangTable.L0 (spanCodes (frozenWangBasis i)) = frozenWangLower i :=
  small_representative_exact i hi

example (i : Fin 496) (hi : 478 ≤ i.val)
    (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hW : frozenWangTable.OrbitImage i W) : frozenWangTable.L0 W = frozenWangLower i :=
  exact_on_orbit i (small_representative_exact i hi) hW

example (i j : Fin 496) (hi : 478 ≤ i.val) (hj : 478 ≤ j.val)
    (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hWi : frozenWangTable.OrbitImage i W) (hWj : frozenWangTable.OrbitImage j W) :
    frozenWangLower i = frozenWangLower j := labels_eq_of_small_overlap i j hi hj W hWi hWj

/-- info: 'QiushiMatmul.FrozenLabel.label_consistent_iff_exact_representatives' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms label_consistent_iff_exact_representatives

/-- info: 'QiushiMatmul.FrozenLabel.exact_of_label_consistent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exact_of_label_consistent

/-- info: 'QiushiMatmul.FrozenLabel.small_representative_exact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms small_representative_exact

/-- info: 'QiushiMatmul.FrozenLabel.labels_eq_of_small_overlap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms labels_eq_of_small_overlap
