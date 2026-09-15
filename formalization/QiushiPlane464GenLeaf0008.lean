import QiushiPlane464GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane464GenLeaf0008Refs : Fin 51 → RowRef 202 50 := ![.occ 13, .occ 28, .occ 30, .occ 32, .occ 34, .occ 37, .occ 54, .occ 55, .occ 56, .occ 57, .occ 61, .occ 66, .occ 67, .occ 73, .occ 80, .occ 87, .occ 93, .occ 103, .occ 104, .occ 106, .occ 107, .occ 120, .occ 121, .occ 131, .occ 132, .occ 136, .occ 146, .occ 156, .occ 176, .occ 180, .occ 181, .occ 182, .occ 183, .occ 184, .occ 185, .occ 186, .occ 187, .occ 196, .occ 200, .occ 201, .sumGe, .nonneg 0, .nonneg 7, .nonneg 12, .nonneg 27, .nonneg 32, .nonneg 39, .nonneg 46, .nonneg 48, .branchGe 1 (1), .branchGe 49 (1)]

def plane464GenLeaf0008Mult : Fin 51 → Nat := ![132, 66, 46, 58, 54, 24, 34, 160, 250, 216, 28, 4, 86, 12, 56, 44, 224, 144, 278, 536, 468, 85, 75, 12, 50, 38, 4, 50, 50, 98, 76, 93, 93, 44, 202, 33, 17, 12, 118, 182, 586, 1378, 230, 316, 28, 270, 118, 242, 118, 674, 2256]

theorem plane464GenLeaf0008 (x : Fin 50 → Int)
    (hroot : plane464GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_49 : (1 : Int) ≤ x 49)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane464GenLeaf0008Refs i).resolveCoeff plane464GenOccSys j)
    (fun i => (plane464GenLeaf0008Refs i).resolveRhs plane464GenOccSys) plane464GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane464GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 32
  · exact hroot.hOcc 34
  · exact hroot.hOcc 37
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 61
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 73
  · exact hroot.hOcc 80
  · exact hroot.hOcc 87
  · exact hroot.hOcc 93
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 146
  · exact hroot.hOcc 156
  · exact hroot.hOcc 176
  · exact hroot.hOcc 180
  · exact hroot.hOcc 181
  · exact hroot.hOcc 182
  · exact hroot.hOcc 183
  · exact hroot.hOcc 184
  · exact hroot.hOcc 185
  · exact hroot.hOcc 186
  · exact hroot.hOcc 187
  · exact hroot.hOcc 196
  · exact hroot.hOcc 200
  · exact hroot.hOcc 201
  · change (∑ j, (-1 : Int) * x j) ≤ -plane464GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (12 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (27 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (39 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (46 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (48 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (1 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (49 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_49

end QiushiMatmul
