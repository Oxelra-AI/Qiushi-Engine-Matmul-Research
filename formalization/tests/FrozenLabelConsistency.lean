import QiushiFrozenLabelConsistency

open QiushiMatmul QiushiMatmul.FrozenLabel

example (i j : Fin 496)
    (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hi : frozenWangTable.OrbitImage i W) (hj : frozenWangTable.OrbitImage j W) :
    frozenWangLower i = frozenWangLower j := labels_eq_of_overlap i j W hi hj

example : ∀ (i j : Fin 496)
    (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2))),
    frozenWangTable.OrbitImage i W → frozenWangTable.OrbitImage j W →
      frozenWangLower i = frozenWangLower j := frozen_labels_consistent

example (i : Fin 496) :
    frozenWangTable.L0 (spanCodes (frozenWangBasis i)) = frozenWangLower i :=
  all_representatives_exact i

example (i : Fin 496)
    (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hi : frozenWangTable.OrbitImage i W) : frozenWangTable.L0 W = frozenWangLower i :=
  L0_exact_of_orbit i W hi

example (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hW : ∃ i : Fin 496, frozenWangTable.OrbitImage i W) :
    ∃ i : Fin 496, frozenWangTable.OrbitImage i W ∧ frozenWangTable.L0 W = frozenWangLower i := by
  obtain ⟨i, hi⟩ := hW
  exact ⟨i, hi, L0_exact_of_orbit i W hi⟩

/-- info: 'QiushiMatmul.FrozenLabel.labels_eq_of_overlap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms labels_eq_of_overlap

/-- info: 'QiushiMatmul.FrozenLabel.frozen_labels_consistent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms frozen_labels_consistent

/-- info: 'QiushiMatmul.FrozenLabel.all_representatives_exact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms all_representatives_exact

/-- info: 'QiushiMatmul.FrozenLabel.L0_exact_of_orbit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms L0_exact_of_orbit
