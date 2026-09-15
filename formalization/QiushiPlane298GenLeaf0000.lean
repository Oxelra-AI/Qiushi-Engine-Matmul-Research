import QiushiPlane298GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane298GenLeaf0000Refs : Fin 11 → RowRef 28 13 := ![.occ 18, .occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 24, .occ 25, .occ 26, .occ 27, .sumGe]

def plane298GenLeaf0000Mult : Fin 11 → Nat := ![1, 3, 2, 3, 1, 2, 1, 1, 1, 2, 3]

theorem plane298GenLeaf0000 (x : Fin 13 → Int)
    (hroot : plane298GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane298GenLeaf0000Refs i).resolveCoeff plane298GenOccSys j)
    (fun i => (plane298GenLeaf0000Refs i).resolveRhs plane298GenOccSys) plane298GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane298GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · change (∑ j, (-1 : Int) * x j) ≤ -plane298GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
