import QiushiPlane452GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane452GenLeaf0004Refs : Fin 32 → RowRef 117 35 := ![.occ 28, .occ 30, .occ 31, .occ 32, .occ 33, .occ 35, .occ 37, .occ 43, .occ 44, .occ 45, .occ 47, .occ 53, .occ 68, .occ 74, .occ 75, .occ 77, .occ 79, .occ 81, .occ 82, .occ 83, .occ 84, .occ 86, .occ 87, .occ 101, .occ 104, .occ 109, .occ 110, .occ 111, .occ 113, .occ 114, .sumGe, .branchGe 8 (1)]

def plane452GenLeaf0004Mult : Fin 32 → Nat := ![30, 48, 14, 18, 2, 48, 36, 4, 8, 48, 16, 2, 48, 18, 18, 48, 2, 1, 16, 14, 17, 15, 17, 12, 12, 14, 18, 18, 16, 30, 48, 336]

theorem plane452GenLeaf0004 (x : Fin 35 → Int)
    (hroot : plane452GenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane452GenLeaf0004Refs i).resolveCoeff plane452GenOccSys j)
    (fun i => (plane452GenLeaf0004Refs i).resolveRhs plane452GenOccSys) plane452GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane452GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 35
  · exact hroot.hOcc 37
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 47
  · exact hroot.hOcc 53
  · exact hroot.hOcc 68
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 77
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 101
  · exact hroot.hOcc 104
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · change (∑ j, (-1 : Int) * x j) ≤ -plane452GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 35) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
