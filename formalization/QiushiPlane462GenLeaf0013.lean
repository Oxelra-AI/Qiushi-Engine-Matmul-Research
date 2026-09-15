import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0013Refs : Fin 63 → RowRef 294 62 := ![.occ 18, .occ 30, .occ 68, .occ 70, .occ 71, .occ 73, .occ 74, .occ 80, .occ 85, .occ 86, .occ 97, .occ 99, .occ 109, .occ 110, .occ 115, .occ 119, .occ 126, .occ 127, .occ 134, .occ 146, .occ 148, .occ 149, .occ 151, .occ 158, .occ 163, .occ 165, .occ 171, .occ 173, .occ 175, .occ 176, .occ 179, .occ 191, .occ 194, .occ 203, .occ 206, .occ 227, .occ 235, .occ 240, .occ 244, .occ 259, .occ 260, .occ 266, .occ 267, .occ 271, .occ 276, .occ 281, .occ 286, .occ 288, .sumGe, .nonneg 0, .nonneg 7, .nonneg 11, .nonneg 13, .nonneg 19, .nonneg 38, .nonneg 48, .nonneg 54, .nonneg 55, .branchGe 3 (1), .branchGe 5 (1), .branchGe 24 (1), .branchLe 27 (0), .branchLe 34 (1)]

def plane462GenLeaf0013Mult : Fin 63 → Nat := ![105536, 392216, 358216, 17896, 213020, 229924, 401796, 396456, 282452, 131484, 224532, 219780, 300844, 214024, 58368, 98337, 4164, 84996, 110338, 169312, 49854, 93044, 114962, 16589, 240167, 311221, 39380, 315296, 22402, 25280, 157532, 81652, 69848, 92122, 295398, 27722, 97594, 34872, 103056, 82232, 2878, 34344, 92136, 367405, 146736, 214378, 324843, 13622, 1503896, 859176, 745840, 15928, 376800, 102320, 287656, 317760, 572280, 71016, 448336, 1447384, 2526696, 1503896, 1350280]

theorem plane462GenLeaf0013 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0013Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0013Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 18
  · exact hroot.hOcc 30
  · exact hroot.hOcc 68
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 80
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 97
  · exact hroot.hOcc 99
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 115
  · exact hroot.hOcc 119
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 134
  · exact hroot.hOcc 146
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 151
  · exact hroot.hOcc 158
  · exact hroot.hOcc 163
  · exact hroot.hOcc 165
  · exact hroot.hOcc 171
  · exact hroot.hOcc 173
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 179
  · exact hroot.hOcc 191
  · exact hroot.hOcc 194
  · exact hroot.hOcc 203
  · exact hroot.hOcc 206
  · exact hroot.hOcc 227
  · exact hroot.hOcc 235
  · exact hroot.hOcc 240
  · exact hroot.hOcc 244
  · exact hroot.hOcc 259
  · exact hroot.hOcc 260
  · exact hroot.hOcc 266
  · exact hroot.hOcc 267
  · exact hroot.hOcc 271
  · exact hroot.hOcc 276
  · exact hroot.hOcc 281
  · exact hroot.hOcc 286
  · exact hroot.hOcc 288
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (11 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (13 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (19 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (38 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (48 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (54 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (55 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (5 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (24 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (27 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (34 : Fin 62) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_34

end QiushiMatmul
