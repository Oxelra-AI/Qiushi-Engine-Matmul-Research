import QiushiPlane472GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane472GenLeaf0011Refs : Fin 63 → RowRef 242 62 := ![.occ 3, .occ 4, .occ 7, .occ 8, .occ 11, .occ 14, .occ 16, .occ 32, .occ 40, .occ 45, .occ 52, .occ 54, .occ 62, .occ 64, .occ 65, .occ 76, .occ 80, .occ 87, .occ 94, .occ 99, .occ 105, .occ 107, .occ 108, .occ 109, .occ 111, .occ 112, .occ 115, .occ 120, .occ 121, .occ 127, .occ 142, .occ 144, .occ 188, .occ 189, .occ 191, .occ 196, .occ 199, .occ 200, .occ 221, .occ 223, .occ 228, .occ 229, .occ 233, .occ 237, .occ 240, .sumGe, .nonneg 18, .nonneg 24, .nonneg 27, .nonneg 30, .nonneg 31, .nonneg 32, .nonneg 36, .nonneg 42, .nonneg 50, .nonneg 52, .nonneg 53, .nonneg 54, .nonneg 55, .nonneg 59, .nonneg 61, .branchGe 60 (1), .branchGe 6 (1)]

def plane472GenLeaf0011Mult : Fin 63 → Nat := ![669, 155, 4234, 1300, 5228, 212, 1893, 2090, 2356, 116, 1742, 4603, 503, 2478, 525, 2331, 1273, 815, 708, 497, 1185, 1073, 2003, 2076, 2233, 1549, 1798, 387, 988, 1361, 170, 541, 708, 117, 2379, 2351, 1325, 55, 377, 731, 497, 95, 632, 613, 12, 5461, 1160, 708, 1746, 2630, 327, 1214, 1713, 2252, 2402, 1866, 1672, 1516, 1425, 314, 825, 18919, 24205]

theorem plane472GenLeaf0011 (x : Fin 62 → Int)
    (hroot : plane472GenOccSys.RootHolds x)
    (hLB_60 : (1 : Int) ≤ x 60)
    (hLB_6 : (1 : Int) ≤ x 6)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane472GenLeaf0011Refs i).resolveCoeff plane472GenOccSys j)
    (fun i => (plane472GenLeaf0011Refs i).resolveRhs plane472GenOccSys) plane472GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane472GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 4
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 11
  · exact hroot.hOcc 14
  · exact hroot.hOcc 16
  · exact hroot.hOcc 32
  · exact hroot.hOcc 40
  · exact hroot.hOcc 45
  · exact hroot.hOcc 52
  · exact hroot.hOcc 54
  · exact hroot.hOcc 62
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 76
  · exact hroot.hOcc 80
  · exact hroot.hOcc 87
  · exact hroot.hOcc 94
  · exact hroot.hOcc 99
  · exact hroot.hOcc 105
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 115
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 188
  · exact hroot.hOcc 189
  · exact hroot.hOcc 191
  · exact hroot.hOcc 196
  · exact hroot.hOcc 199
  · exact hroot.hOcc 200
  · exact hroot.hOcc 221
  · exact hroot.hOcc 223
  · exact hroot.hOcc 228
  · exact hroot.hOcc 229
  · exact hroot.hOcc 233
  · exact hroot.hOcc 237
  · exact hroot.hOcc 240
  · change (∑ j, (-1 : Int) * x j) ≤ -plane472GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (24 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (27 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (31 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (36 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (42 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (50 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (54 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (55 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (61 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (60 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_60
  · change (∑ k, (if k = (6 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
