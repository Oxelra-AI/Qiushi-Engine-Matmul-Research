import QiushiFrozenLabelIncidence

open QiushiMatmul QiushiMatmul.FrozenLabel QiushiMatmul.PlaneOrbit

example (bs : List Nat) (a : Fin 512) (s t : Nat) :
    codeNeighborCount bs a s t = Nat.card
      {B : spanCodes bs // B.val.rank = s ∧ (codeMat a.val + B.val).rank = t} :=
  codeNeighborCount_correct bs a s t

example (i j : Fin 496)
    (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hi : frozenWangTable.OrbitImage i W) (hj : frozenWangTable.OrbitImage j W) :
    pointSignature (frozenWangBasis i) = pointSignature (frozenWangBasis j) :=
  pointSignature_eq_of_overlap i j W hi hj

example (i j : Fin 496)
    (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hi : frozenWangTable.OrbitImage i W) (hj : frozenWangTable.OrbitImage j W) :
    pointKey (frozenWangBasis i) = pointKey (frozenWangBasis j) :=
  pointKey_eq_of_overlap i j W hi hj

example (k : Fin 14) (bs : List Nat) : planeIncidence k bs = Nat.card
    {U : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)) //
      Equivalent (FullClassification.frozenRep k) U ∧ U ≤ spanCodes bs} :=
  planeIncidence_correct k bs

example (k : Fin 14) (i j : Fin 496)
    (W : Submodule (ZMod 2) (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hi : frozenWangTable.OrbitImage i W) (hj : frozenWangTable.OrbitImage j W) :
    planeIncidence k (frozenWangBasis i) = planeIncidence k (frozenWangBasis j) :=
  planeIncidence_eq_of_overlap k i j W hi hj

example : pointKey [1] = 111880246 := by decide +kernel

/-- info: 'QiushiMatmul.FrozenLabel.pointKey_eq_of_overlap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pointKey_eq_of_overlap

/-- info: 'QiushiMatmul.FrozenLabel.planeIncidence_correct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms planeIncidence_correct

/-- info: 'QiushiMatmul.FrozenLabel.planeIncidence_eq_of_overlap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms planeIncidence_eq_of_overlap
