import QiushiPlane456GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane456GenLeaf0003Refs : Fin 64 → RowRef 248 63 := ![.occ 5, .occ 14, .occ 33, .occ 36, .occ 58, .occ 59, .occ 72, .occ 76, .occ 77, .occ 82, .occ 83, .occ 89, .occ 90, .occ 91, .occ 100, .occ 107, .occ 113, .occ 114, .occ 124, .occ 126, .occ 132, .occ 134, .occ 135, .occ 145, .occ 154, .occ 157, .occ 163, .occ 171, .occ 172, .occ 174, .occ 181, .occ 187, .occ 216, .occ 218, .occ 231, .occ 232, .occ 235, .occ 236, .occ 239, .occ 240, .occ 241, .occ 242, .sumGe, .nonneg 19, .nonneg 21, .nonneg 28, .nonneg 29, .nonneg 32, .nonneg 34, .nonneg 37, .nonneg 42, .nonneg 44, .nonneg 48, .nonneg 50, .nonneg 51, .nonneg 53, .nonneg 55, .nonneg 58, .branchLe 24 (0), .branchLe 31 (0), .branchLe 57 (0), .branchLe 54 (0), .branchGe 9 (1), .branchGe 4 (1)]

def plane456GenLeaf0003Mult : Fin 64 → Nat := ![14770, 17540, 8396, 3726, 7094, 6434, 3030, 24150, 10286, 17908, 12372, 1206, 7602, 2542, 17568, 4048, 1596, 742, 3804, 9188, 24300, 8678, 18754, 7380, 3436, 4972, 1026, 7070, 17910, 68, 5982, 888, 2618, 7204, 2853, 4079, 12051, 6517, 5567, 9571, 4787, 5333, 52690, 2310, 31178, 33802, 18324, 10034, 1480, 23414, 18618, 14792, 20072, 3210, 13668, 22620, 22920, 21226, 17486, 13830, 42570, 34682, 87598, 94074]

theorem plane456GenLeaf0003 (x : Fin 63 → Int)
    (hroot : plane456GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_57 : x 57 ≤ (0 : Int))
    (hUB_54 : x 54 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane456GenLeaf0003Refs i).resolveCoeff plane456GenOccSys j)
    (fun i => (plane456GenLeaf0003Refs i).resolveRhs plane456GenOccSys) plane456GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane456GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 14
  · exact hroot.hOcc 33
  · exact hroot.hOcc 36
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 72
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 100
  · exact hroot.hOcc 107
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 145
  · exact hroot.hOcc 154
  · exact hroot.hOcc 157
  · exact hroot.hOcc 163
  · exact hroot.hOcc 171
  · exact hroot.hOcc 172
  · exact hroot.hOcc 174
  · exact hroot.hOcc 181
  · exact hroot.hOcc 187
  · exact hroot.hOcc 216
  · exact hroot.hOcc 218
  · exact hroot.hOcc 231
  · exact hroot.hOcc 232
  · exact hroot.hOcc 235
  · exact hroot.hOcc 236
  · exact hroot.hOcc 239
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · exact hroot.hOcc 242
  · change (∑ j, (-1 : Int) * x j) ≤ -plane456GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (28 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (29 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (50 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (53 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (58 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (31 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (57 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_57
  · change (∑ k, (if k = (54 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_54
  · change (∑ k, (if k = (9 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (4 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
