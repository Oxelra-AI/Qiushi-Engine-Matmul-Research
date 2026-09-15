import QiushiPlane461GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane461GenLeaf0005Refs : Fin 63 → RowRef 151 62 := ![.occ 4, .occ 5, .occ 6, .occ 7, .occ 9, .occ 16, .occ 22, .occ 27, .occ 28, .occ 30, .occ 35, .occ 37, .occ 38, .occ 39, .occ 42, .occ 43, .occ 44, .occ 45, .occ 48, .occ 50, .occ 52, .occ 53, .occ 54, .occ 55, .occ 56, .occ 59, .occ 60, .occ 61, .occ 71, .occ 72, .occ 87, .occ 88, .occ 91, .occ 92, .occ 95, .occ 96, .occ 97, .occ 115, .occ 116, .occ 118, .occ 130, .occ 138, .occ 139, .occ 141, .occ 143, .occ 145, .occ 147, .occ 149, .sumGe, .nonneg 6, .nonneg 9, .nonneg 17, .nonneg 23, .nonneg 32, .nonneg 33, .nonneg 36, .nonneg 39, .nonneg 51, .nonneg 53, .nonneg 56, .nonneg 60, .branchGe 16 (1), .branchGe 48 (1)]

def plane461GenLeaf0005Mult : Fin 63 → Nat := ![4075, 3468, 831, 1511, 1218, 1950, 4027, 6012, 1257, 6115, 2459, 2071, 5895, 2947, 7011, 945, 351, 3495, 822, 704, 3286, 1594, 431, 2420, 1183, 585, 655, 142, 709, 2596, 907, 717, 1492, 672, 250, 2863, 1598, 3190, 490, 647, 1488, 277, 373, 1805, 1269, 673, 766, 597, 10793, 12651, 11806, 3149, 2073, 3279, 652, 1950, 5431, 8457, 3912, 1695, 1660, 6090, 40169]

theorem plane461GenLeaf0005 (x : Fin 62 → Int)
    (hroot : plane461GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_48 : (1 : Int) ≤ x 48)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane461GenLeaf0005Refs i).resolveCoeff plane461GenOccSys j)
    (fun i => (plane461GenLeaf0005Refs i).resolveRhs plane461GenOccSys) plane461GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane461GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 5
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 16
  · exact hroot.hOcc 22
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 35
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 48
  · exact hroot.hOcc 50
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 130
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 145
  · exact hroot.hOcc 147
  · exact hroot.hOcc 149
  · change (∑ j, (-1 : Int) * x j) ≤ -plane461GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (9 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (17 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (23 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (56 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (60 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (16 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (48 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_48

end QiushiMatmul
