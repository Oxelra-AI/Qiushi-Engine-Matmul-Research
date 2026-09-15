import QiushiPlane425GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane425GenLeaf0008Refs : Fin 59 → RowRef 202 58 := ![.occ 7, .occ 16, .occ 21, .occ 25, .occ 32, .occ 35, .occ 36, .occ 41, .occ 47, .occ 52, .occ 55, .occ 59, .occ 62, .occ 66, .occ 69, .occ 74, .occ 83, .occ 84, .occ 87, .occ 92, .occ 95, .occ 120, .occ 126, .occ 130, .occ 140, .occ 146, .occ 153, .occ 157, .occ 158, .occ 161, .occ 165, .occ 168, .occ 172, .occ 180, .occ 186, .occ 190, .occ 191, .occ 192, .occ 195, .occ 196, .occ 198, .occ 199, .sumGe, .nonneg 2, .nonneg 3, .nonneg 13, .nonneg 14, .nonneg 15, .nonneg 19, .nonneg 20, .nonneg 21, .nonneg 36, .nonneg 37, .nonneg 41, .nonneg 48, .nonneg 52, .nonneg 56, .branchGe 17 (1), .branchGe 9 (1)]

def plane425GenLeaf0008Mult : Fin 59 → Nat := ![4615, 4073, 9147, 1064, 1592, 1824, 1440, 3835, 3985, 2923, 4289, 6639, 9685, 1937, 11254, 364, 7638, 5657, 1686, 1253, 5466, 3197, 1064, 826, 10385, 229, 4756, 2276, 1444, 4177, 151, 3426, 4261, 1444, 4299, 4048, 433, 162, 1132, 865, 405, 1047, 16709, 1707, 11869, 8410, 6298, 5196, 4047, 6749, 2596, 606, 1912, 3441, 3529, 4049, 2481, 52105, 60373]

theorem plane425GenLeaf0008 (x : Fin 58 → Int)
    (hroot : plane425GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_9 : (1 : Int) ≤ x 9)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane425GenLeaf0008Refs i).resolveCoeff plane425GenOccSys j)
    (fun i => (plane425GenLeaf0008Refs i).resolveRhs plane425GenOccSys) plane425GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane425GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 16
  · exact hroot.hOcc 21
  · exact hroot.hOcc 25
  · exact hroot.hOcc 32
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 41
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 55
  · exact hroot.hOcc 59
  · exact hroot.hOcc 62
  · exact hroot.hOcc 66
  · exact hroot.hOcc 69
  · exact hroot.hOcc 74
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 87
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 120
  · exact hroot.hOcc 126
  · exact hroot.hOcc 130
  · exact hroot.hOcc 140
  · exact hroot.hOcc 146
  · exact hroot.hOcc 153
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 161
  · exact hroot.hOcc 165
  · exact hroot.hOcc 168
  · exact hroot.hOcc 172
  · exact hroot.hOcc 180
  · exact hroot.hOcc 186
  · exact hroot.hOcc 190
  · exact hroot.hOcc 191
  · exact hroot.hOcc 192
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · change (∑ j, (-1 : Int) * x j) ≤ -plane425GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (3 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (13 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (21 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (37 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (41 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (48 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (52 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (56 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (9 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
