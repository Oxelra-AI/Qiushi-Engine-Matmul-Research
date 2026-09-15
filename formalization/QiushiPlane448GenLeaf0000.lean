import QiushiPlane448GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane448GenLeaf0000Refs : Fin 19 → RowRef 56 22 := ![.occ 38, .occ 39, .occ 40, .occ 41, .occ 42, .occ 43, .occ 44, .occ 45, .occ 46, .occ 47, .occ 48, .occ 49, .occ 50, .occ 51, .occ 52, .occ 53, .occ 54, .occ 55, .sumGe]

def plane448GenLeaf0000Mult : Fin 19 → Nat := ![3, 3, 3, 3, 3, 1, 3, 3, 1, 2, 1, 1, 4, 1, 1, 1, 2, 2, 6]

theorem plane448GenLeaf0000 (x : Fin 22 → Int)
    (hroot : plane448GenOccSys.RootHolds x)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane448GenLeaf0000Refs i).resolveCoeff plane448GenOccSys j)
    (fun i => (plane448GenLeaf0000Refs i).resolveRhs plane448GenOccSys) plane448GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane448GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · change (∑ j, (-1 : Int) * x j) ≤ -plane448GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal

end QiushiMatmul
