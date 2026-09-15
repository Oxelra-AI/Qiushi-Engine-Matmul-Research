import QiushiPlane456GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane456GenLeaf0008Refs : Fin 64 → RowRef 248 63 := ![.occ 9, .occ 10, .occ 15, .occ 19, .occ 26, .occ 36, .occ 40, .occ 49, .occ 62, .occ 72, .occ 82, .occ 83, .occ 85, .occ 86, .occ 87, .occ 91, .occ 92, .occ 93, .occ 98, .occ 101, .occ 106, .occ 112, .occ 116, .occ 117, .occ 123, .occ 129, .occ 133, .occ 134, .occ 136, .occ 140, .occ 145, .occ 160, .occ 164, .occ 172, .occ 176, .occ 185, .occ 196, .occ 200, .occ 217, .occ 218, .occ 219, .occ 220, .occ 229, .occ 234, .occ 241, .occ 246, .sumGe, .nonneg 7, .nonneg 21, .nonneg 23, .nonneg 26, .nonneg 28, .nonneg 42, .nonneg 44, .nonneg 48, .nonneg 49, .nonneg 51, .nonneg 53, .nonneg 55, .nonneg 59, .nonneg 60, .branchLe 24 (0), .branchGe 31 (1), .branchLe 6 (0)]

def plane456GenLeaf0008Mult : Fin 64 → Nat := ![1302, 3265, 1992, 770, 371, 1363, 1415, 2350, 254, 806, 185, 132, 1098, 524, 1448, 774, 156, 401, 1701, 162, 468, 401, 189, 741, 998, 1242, 315, 741, 687, 668, 197, 878, 531, 493, 1253, 275, 55, 126, 88, 185, 280, 281, 186, 550, 781, 293, 3451, 76, 627, 1880, 1848, 1725, 2361, 1720, 216, 8, 1412, 1790, 132, 548, 1188, 2244, 16857, 1840]

theorem plane456GenLeaf0008 (x : Fin 63 → Int)
    (hroot : plane456GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane456GenLeaf0008Refs i).resolveCoeff plane456GenOccSys j)
    (fun i => (plane456GenLeaf0008Refs i).resolveRhs plane456GenOccSys) plane456GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane456GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 15
  · exact hroot.hOcc 19
  · exact hroot.hOcc 26
  · exact hroot.hOcc 36
  · exact hroot.hOcc 40
  · exact hroot.hOcc 49
  · exact hroot.hOcc 62
  · exact hroot.hOcc 72
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 93
  · exact hroot.hOcc 98
  · exact hroot.hOcc 101
  · exact hroot.hOcc 106
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 140
  · exact hroot.hOcc 145
  · exact hroot.hOcc 160
  · exact hroot.hOcc 164
  · exact hroot.hOcc 172
  · exact hroot.hOcc 176
  · exact hroot.hOcc 185
  · exact hroot.hOcc 196
  · exact hroot.hOcc 200
  · exact hroot.hOcc 217
  · exact hroot.hOcc 218
  · exact hroot.hOcc 219
  · exact hroot.hOcc 220
  · exact hroot.hOcc 229
  · exact hroot.hOcc 234
  · exact hroot.hOcc 241
  · exact hroot.hOcc 246
  · change (∑ j, (-1 : Int) * x j) ≤ -plane456GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (23 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (53 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (60 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (31 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (6 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6

end QiushiMatmul
