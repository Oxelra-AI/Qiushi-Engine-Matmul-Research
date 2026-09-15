import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0019Refs : Fin 63 → RowRef 294 62 := ![.occ 14, .occ 32, .occ 35, .occ 40, .occ 67, .occ 72, .occ 73, .occ 74, .occ 77, .occ 78, .occ 80, .occ 86, .occ 88, .occ 90, .occ 91, .occ 100, .occ 103, .occ 110, .occ 118, .occ 119, .occ 124, .occ 131, .occ 151, .occ 155, .occ 158, .occ 162, .occ 165, .occ 167, .occ 176, .occ 177, .occ 191, .occ 206, .occ 212, .occ 213, .occ 217, .occ 227, .occ 243, .occ 250, .occ 258, .occ 271, .occ 274, .occ 278, .occ 286, .occ 290, .sumGe, .nonneg 7, .nonneg 8, .nonneg 17, .nonneg 19, .nonneg 20, .nonneg 26, .nonneg 29, .nonneg 33, .nonneg 38, .nonneg 54, .nonneg 59, .branchGe 3 (1), .branchGe 5 (1), .branchGe 24 (1), .branchGe 27 (1), .branchGe 9 (1), .branchLe 6 (0), .branchLe 34 (1)]

def plane462GenLeaf0019Mult : Fin 63 → Nat := ![20586, 4356, 5688, 15732, 18492, 1968, 1308, 26370, 27150, 9396, 58878, 8418, 555, 7584, 70425, 52473, 16611, 62052, 2956, 19268, 34183, 16473, 6802, 3874, 3754, 1490, 50827, 35357, 24252, 16116, 8472, 68484, 10020, 10752, 40836, 2064, 3534, 15852, 6222, 11398, 23124, 20089, 48169, 11250, 176076, 55728, 205368, 84168, 94296, 21900, 20868, 33936, 68640, 15168, 33168, 34848, 199584, 68400, 154812, 100476, 135828, 176076, 151824]

theorem plane462GenLeaf0019 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0019Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0019Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0019Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0019Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 32
  · exact hroot.hOcc 35
  · exact hroot.hOcc 40
  · exact hroot.hOcc 67
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 110
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 124
  · exact hroot.hOcc 131
  · exact hroot.hOcc 151
  · exact hroot.hOcc 155
  · exact hroot.hOcc 158
  · exact hroot.hOcc 162
  · exact hroot.hOcc 165
  · exact hroot.hOcc 167
  · exact hroot.hOcc 176
  · exact hroot.hOcc 177
  · exact hroot.hOcc 191
  · exact hroot.hOcc 206
  · exact hroot.hOcc 212
  · exact hroot.hOcc 213
  · exact hroot.hOcc 217
  · exact hroot.hOcc 227
  · exact hroot.hOcc 243
  · exact hroot.hOcc 250
  · exact hroot.hOcc 258
  · exact hroot.hOcc 271
  · exact hroot.hOcc 274
  · exact hroot.hOcc 278
  · exact hroot.hOcc 286
  · exact hroot.hOcc 290
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (17 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (26 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (29 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (33 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (38 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (54 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (5 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (24 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (27 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (9 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (6 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (34 : Fin 62) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_34

end QiushiMatmul
