import QiushiPlane447GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane447GenLeaf0000Refs : Fin 6 → RowRef 55 13 := ![.occ 50, .occ 51, .occ 52, .occ 53, .occ 54, .sumGe]

def plane447GenLeaf0000Mult : Fin 6 → Nat := ![1, 1, 1, 1, 1, 1]

theorem plane447GenLeaf0000 (x : Fin 13 → Int)
    (hroot : plane447GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane447GenLeaf0000Refs i).resolveCoeff plane447GenOccSys j)
    (fun i => (plane447GenLeaf0000Refs i).resolveRhs plane447GenOccSys) plane447GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane447GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · change (∑ j, (-1 : Int) * x j) ≤ -plane447GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
