import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0008Refs : Fin 63 → RowRef 294 62 := ![.occ 4, .occ 7, .occ 10, .occ 47, .occ 53, .occ 54, .occ 67, .occ 70, .occ 73, .occ 76, .occ 78, .occ 84, .occ 86, .occ 88, .occ 89, .occ 92, .occ 95, .occ 96, .occ 102, .occ 108, .occ 110, .occ 112, .occ 124, .occ 126, .occ 128, .occ 134, .occ 144, .occ 154, .occ 156, .occ 159, .occ 164, .occ 175, .occ 184, .occ 193, .occ 195, .occ 200, .occ 203, .occ 220, .occ 229, .occ 232, .occ 263, .occ 271, .occ 275, .occ 276, .occ 283, .occ 284, .occ 290, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 17, .nonneg 30, .nonneg 32, .nonneg 33, .nonneg 39, .nonneg 40, .nonneg 47, .nonneg 57, .branchGe 3 (1), .branchLe 5 (0), .branchLe 2 (0), .branchGe 43 (1)]

def plane462GenLeaf0008Mult : Fin 63 → Nat := ![15728, 1744, 2460, 14112, 17628, 7754, 4872, 10556, 13140, 5288, 24776, 20460, 13928, 21936, 2200, 9456, 15104, 144, 6504, 28392, 4728, 1504, 9000, 18139, 5174, 1470, 4388, 1600, 12444, 4134, 144, 19460, 11392, 15834, 13695, 6978, 14752, 5874, 10181, 16444, 11775, 12423, 9156, 19846, 11658, 11900, 6625, 99760, 18160, 10704, 31968, 4584, 15440, 22224, 18552, 11404, 14320, 18912, 23496, 17884, 99760, 68256, 199892]

theorem plane462GenLeaf0008 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0008Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0008Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 7
  · exact hroot.hOcc 10
  · exact hroot.hOcc 47
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 67
  · exact hroot.hOcc 70
  · exact hroot.hOcc 73
  · exact hroot.hOcc 76
  · exact hroot.hOcc 78
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 102
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 134
  · exact hroot.hOcc 144
  · exact hroot.hOcc 154
  · exact hroot.hOcc 156
  · exact hroot.hOcc 159
  · exact hroot.hOcc 164
  · exact hroot.hOcc 175
  · exact hroot.hOcc 184
  · exact hroot.hOcc 193
  · exact hroot.hOcc 195
  · exact hroot.hOcc 200
  · exact hroot.hOcc 203
  · exact hroot.hOcc 220
  · exact hroot.hOcc 229
  · exact hroot.hOcc 232
  · exact hroot.hOcc 263
  · exact hroot.hOcc 271
  · exact hroot.hOcc 275
  · exact hroot.hOcc 276
  · exact hroot.hOcc 283
  · exact hroot.hOcc 284
  · exact hroot.hOcc 290
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (17 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (47 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (5 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (2 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (43 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43

end QiushiMatmul
