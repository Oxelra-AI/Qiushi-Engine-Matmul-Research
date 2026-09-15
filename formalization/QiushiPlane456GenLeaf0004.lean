import QiushiPlane456GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane456GenLeaf0004Refs : Fin 64 → RowRef 248 63 := ![.occ 1, .occ 4, .occ 14, .occ 25, .occ 27, .occ 28, .occ 29, .occ 30, .occ 31, .occ 36, .occ 43, .occ 53, .occ 55, .occ 65, .occ 66, .occ 68, .occ 71, .occ 72, .occ 82, .occ 88, .occ 90, .occ 93, .occ 96, .occ 97, .occ 98, .occ 99, .occ 103, .occ 105, .occ 114, .occ 123, .occ 130, .occ 134, .occ 137, .occ 144, .occ 145, .occ 154, .occ 155, .occ 162, .occ 175, .occ 182, .occ 188, .occ 189, .occ 197, .occ 205, .occ 207, .occ 221, .occ 222, .occ 223, .occ 226, .occ 230, .occ 231, .occ 235, .sumGe, .nonneg 26, .nonneg 28, .nonneg 32, .nonneg 37, .nonneg 42, .nonneg 53, .nonneg 59, .branchLe 24 (0), .branchLe 31 (0), .branchLe 57 (0), .branchGe 54 (1)]

def plane456GenLeaf0004Mult : Fin 64 → Nat := ![1230, 2730, 50, 269, 4907, 1291, 2517, 9669, 1078, 507, 630, 1305, 9661, 4951, 152, 1926, 125, 2813, 1425, 2453, 331, 33, 4280, 1235, 9665, 6528, 3456, 373, 1450, 6574, 1722, 108, 7528, 1001, 21, 170, 517, 912, 6770, 4156, 142, 413, 332, 1275, 5244, 993, 1188, 1500, 305, 1641, 3811, 328, 13825, 3799, 3189, 948, 2229, 2350, 416, 6352, 3726, 4649, 12550, 79540]

theorem plane456GenLeaf0004 (x : Fin 63 → Int)
    (hroot : plane456GenOccSys.RootHolds x)
    (hLB_54 : (1 : Int) ≤ x 54)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_57 : x 57 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane456GenLeaf0004Refs i).resolveCoeff plane456GenOccSys j)
    (fun i => (plane456GenLeaf0004Refs i).resolveRhs plane456GenOccSys) plane456GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane456GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 4
  · exact hroot.hOcc 14
  · exact hroot.hOcc 25
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 36
  · exact hroot.hOcc 43
  · exact hroot.hOcc 53
  · exact hroot.hOcc 55
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 68
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 82
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 114
  · exact hroot.hOcc 123
  · exact hroot.hOcc 130
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 144
  · exact hroot.hOcc 145
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 162
  · exact hroot.hOcc 175
  · exact hroot.hOcc 182
  · exact hroot.hOcc 188
  · exact hroot.hOcc 189
  · exact hroot.hOcc 197
  · exact hroot.hOcc 205
  · exact hroot.hOcc 207
  · exact hroot.hOcc 221
  · exact hroot.hOcc 222
  · exact hroot.hOcc 223
  · exact hroot.hOcc 226
  · exact hroot.hOcc 230
  · exact hroot.hOcc 231
  · exact hroot.hOcc 235
  · change (∑ j, (-1 : Int) * x j) ≤ -plane456GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (53 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (31 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (57 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_57
  · change (∑ k, (if k = (54 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_54

end QiushiMatmul
