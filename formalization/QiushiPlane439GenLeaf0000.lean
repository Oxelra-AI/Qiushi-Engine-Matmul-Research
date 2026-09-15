import QiushiPlane439GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane439GenLeaf0000Refs : Fin 12 → RowRef 59 13 := ![.occ 48, .occ 49, .occ 50, .occ 51, .occ 52, .occ 53, .occ 54, .occ 55, .occ 56, .occ 57, .occ 58, .sumGe]

def plane439GenLeaf0000Mult : Fin 12 → Nat := ![1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2]

theorem plane439GenLeaf0000 (x : Fin 13 → Int)
    (hroot : plane439GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane439GenLeaf0000Refs i).resolveCoeff plane439GenOccSys j)
    (fun i => (plane439GenLeaf0000Refs i).resolveRhs plane439GenOccSys) plane439GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane439GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · change (∑ j, (-1 : Int) * x j) ≤ -plane439GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
