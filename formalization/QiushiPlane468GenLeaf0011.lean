import QiushiPlane468GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane468GenLeaf0011Refs : Fin 63 → RowRef 253 62 := ![.occ 1, .occ 2, .occ 11, .occ 17, .occ 31, .occ 33, .occ 41, .occ 45, .occ 66, .occ 68, .occ 71, .occ 73, .occ 74, .occ 75, .occ 90, .occ 98, .occ 103, .occ 105, .occ 109, .occ 110, .occ 121, .occ 123, .occ 124, .occ 130, .occ 133, .occ 135, .occ 136, .occ 148, .occ 154, .occ 161, .occ 168, .occ 174, .occ 182, .occ 210, .occ 229, .occ 233, .occ 235, .occ 238, .occ 239, .occ 241, .occ 244, .occ 245, .occ 246, .occ 248, .occ 251, .occ 252, .sumGe, .nonneg 7, .nonneg 32, .nonneg 34, .nonneg 37, .nonneg 38, .nonneg 39, .nonneg 42, .nonneg 46, .nonneg 53, .nonneg 56, .nonneg 57, .nonneg 59, .nonneg 60, .branchGe 28 (1), .branchLe 36 (0), .branchLe 55 (0)]

def plane468GenLeaf0011Mult : Fin 63 → Nat := ![17100, 11916, 17168, 36952, 33230, 119572, 10492, 31548, 75872, 2636, 47310, 42416, 210090, 12768, 296458, 49128, 47264, 8650, 284092, 27912, 37470, 14916, 51800, 67634, 59402, 25680, 41096, 93496, 3042, 13004, 25160, 9462, 127310, 95652, 177454, 20988, 121536, 20725, 16168, 142967, 18756, 6387, 116405, 97954, 8626, 89258, 521006, 46404, 6634, 61404, 53512, 146014, 118200, 305262, 9204, 315222, 82424, 123910, 95046, 30336, 1644032, 438818, 441694]

theorem plane468GenLeaf0011 (x : Fin 62 → Int)
    (hroot : plane468GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_55 : x 55 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane468GenLeaf0011Refs i).resolveCoeff plane468GenOccSys j)
    (fun i => (plane468GenLeaf0011Refs i).resolveRhs plane468GenOccSys) plane468GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane468GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 2
  · exact hroot.hOcc 11
  · exact hroot.hOcc 17
  · exact hroot.hOcc 31
  · exact hroot.hOcc 33
  · exact hroot.hOcc 41
  · exact hroot.hOcc 45
  · exact hroot.hOcc 66
  · exact hroot.hOcc 68
  · exact hroot.hOcc 71
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 90
  · exact hroot.hOcc 98
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 148
  · exact hroot.hOcc 154
  · exact hroot.hOcc 161
  · exact hroot.hOcc 168
  · exact hroot.hOcc 174
  · exact hroot.hOcc 182
  · exact hroot.hOcc 210
  · exact hroot.hOcc 229
  · exact hroot.hOcc 233
  · exact hroot.hOcc 235
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 241
  · exact hroot.hOcc 244
  · exact hroot.hOcc 245
  · exact hroot.hOcc 246
  · exact hroot.hOcc 248
  · exact hroot.hOcc 251
  · exact hroot.hOcc 252
  · change (∑ j, (-1 : Int) * x j) ≤ -plane468GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (37 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (38 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (42 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (46 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (56 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (60 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (28 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (36 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (55 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_55

end QiushiMatmul
