import QiushiPlane449GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane449GenLeaf0000Refs : Fin 9 → RowRef 56 15 := ![.occ 48, .occ 49, .occ 50, .occ 51, .occ 52, .occ 53, .occ 54, .occ 55, .sumGe]

def plane449GenLeaf0000Mult : Fin 9 → Nat := ![1, 1, 1, 2, 2, 2, 2, 2, 4]

theorem plane449GenLeaf0000 (x : Fin 15 → Int)
    (hroot : plane449GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane449GenLeaf0000Refs i).resolveCoeff plane449GenOccSys j)
    (fun i => (plane449GenLeaf0000Refs i).resolveRhs plane449GenOccSys) plane449GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane449GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · change (∑ j, (-1 : Int) * x j) ≤ -plane449GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
