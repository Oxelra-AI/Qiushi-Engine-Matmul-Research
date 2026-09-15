import QiushiFrozenLabelCollisions

open QiushiMatmul QiushiMatmul.FrozenLabel

example (i j : Fin 496) (hc : (i.val, j.val) ∈ collisionPairs)
    (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2))) :
    ¬ (frozenWangTable.OrbitImage i W ∧ frozenWangTable.OrbitImage j W) := by
  rintro ⟨hi, hj⟩
  exact collisionPairs_no_overlap i j hc W hi hj

example (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hi : frozenWangTable.OrbitImage 129 W) : ¬ frozenWangTable.OrbitImage 133 W := by
  intro hj
  exact collisionPairs_no_overlap 129 133 (by decide +kernel) W hi hj

example (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hi : frozenWangTable.OrbitImage 364 W) : ¬ frozenWangTable.OrbitImage 365 W := by
  intro hj
  exact collisionPairs_no_overlap 364 365 (by decide +kernel) W hi hj

/-- info: 'QiushiMatmul.FrozenLabel.collisionPairs_no_overlap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collisionPairs_no_overlap
