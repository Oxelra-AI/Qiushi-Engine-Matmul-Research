import QiushiPlane455GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane455GenLeaf0003Refs : Fin 49 → RowRef 124 48 := ![.occ 15, .occ 16, .occ 19, .occ 20, .occ 23, .occ 30, .occ 31, .occ 34, .occ 36, .occ 38, .occ 40, .occ 43, .occ 45, .occ 47, .occ 49, .occ 50, .occ 53, .occ 56, .occ 58, .occ 59, .occ 60, .occ 61, .occ 64, .occ 69, .occ 70, .occ 75, .occ 76, .occ 77, .occ 79, .occ 82, .occ 86, .occ 87, .occ 92, .occ 94, .occ 107, .occ 110, .occ 112, .occ 114, .occ 115, .occ 116, .occ 117, .occ 120, .occ 121, .sumGe, .nonneg 22, .nonneg 28, .nonneg 30, .branchGe 14 (1), .branchGe 8 (1)]

def plane455GenLeaf0003Mult : Fin 49 → Nat := ![4780, 3698, 7797, 6531, 1662, 792, 2493, 346, 2493, 4602, 452, 5650, 5360, 4506, 1461, 4931, 1461, 5617, 2311, 3287, 4734, 5130, 432, 3334, 4310, 2186, 814, 1662, 1649, 1121, 1807, 1543, 423, 27, 2787, 2787, 1365, 1677, 4266, 780, 1176, 1677, 537, 13218, 8262, 4542, 4956, 38879, 33697]

theorem plane455GenLeaf0003 (x : Fin 48 → Int)
    (hroot : plane455GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_8 : (1 : Int) ≤ x 8)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane455GenLeaf0003Refs i).resolveCoeff plane455GenOccSys j)
    (fun i => (plane455GenLeaf0003Refs i).resolveRhs plane455GenOccSys) plane455GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane455GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 23
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 38
  · exact hroot.hOcc 40
  · exact hroot.hOcc 43
  · exact hroot.hOcc 45
  · exact hroot.hOcc 47
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 53
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 64
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 79
  · exact hroot.hOcc 82
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 92
  · exact hroot.hOcc 94
  · exact hroot.hOcc 107
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · change (∑ j, (-1 : Int) * x j) ≤ -plane455GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (22 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (30 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (14 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
