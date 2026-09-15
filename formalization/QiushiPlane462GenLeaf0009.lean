import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0009Refs : Fin 63 → RowRef 294 62 := ![.occ 14, .occ 25, .occ 44, .occ 51, .occ 67, .occ 72, .occ 73, .occ 76, .occ 78, .occ 84, .occ 86, .occ 88, .occ 89, .occ 92, .occ 94, .occ 96, .occ 99, .occ 102, .occ 103, .occ 105, .occ 110, .occ 134, .occ 142, .occ 147, .occ 160, .occ 163, .occ 171, .occ 176, .occ 187, .occ 197, .occ 229, .occ 232, .occ 234, .occ 243, .occ 244, .occ 246, .occ 268, .occ 271, .occ 275, .occ 276, .occ 282, .occ 283, .occ 284, .occ 290, .occ 292, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 10, .nonneg 12, .nonneg 13, .nonneg 15, .nonneg 25, .nonneg 39, .nonneg 51, .nonneg 52, .nonneg 53, .nonneg 61, .branchGe 3 (1), .branchLe 5 (0), .branchGe 2 (1), .branchLe 45 (0)]

def plane462GenLeaf0009Mult : Fin 63 → Nat := ![29148, 15486, 7086, 5868, 14876, 24958, 17256, 1328, 13950, 2188, 7602, 19482, 4496, 11046, 4030, 4850, 10506, 5664, 10510, 21818, 14932, 8790, 2508, 972, 6642, 7074, 2076, 4560, 4940, 8874, 3240, 4134, 1326, 2508, 5832, 5836, 14692, 6543, 7360, 12427, 18207, 11717, 3179, 1074, 5117, 77772, 50052, 50568, 59172, 13980, 9708, 4416, 6800, 15400, 17184, 24704, 24240, 43752, 21088, 58500, 77772, 78780, 65304]

theorem plane462GenLeaf0009 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_45 : x 45 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0009Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0009Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 25
  · exact hroot.hOcc 44
  · exact hroot.hOcc 51
  · exact hroot.hOcc 67
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 76
  · exact hroot.hOcc 78
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 92
  · exact hroot.hOcc 94
  · exact hroot.hOcc 96
  · exact hroot.hOcc 99
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 110
  · exact hroot.hOcc 134
  · exact hroot.hOcc 142
  · exact hroot.hOcc 147
  · exact hroot.hOcc 160
  · exact hroot.hOcc 163
  · exact hroot.hOcc 171
  · exact hroot.hOcc 176
  · exact hroot.hOcc 187
  · exact hroot.hOcc 197
  · exact hroot.hOcc 229
  · exact hroot.hOcc 232
  · exact hroot.hOcc 234
  · exact hroot.hOcc 243
  · exact hroot.hOcc 244
  · exact hroot.hOcc 246
  · exact hroot.hOcc 268
  · exact hroot.hOcc 271
  · exact hroot.hOcc 275
  · exact hroot.hOcc 276
  · exact hroot.hOcc 282
  · exact hroot.hOcc 283
  · exact hroot.hOcc 284
  · exact hroot.hOcc 290
  · exact hroot.hOcc 292
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (12 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (13 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (15 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (25 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (52 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (61 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (5 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (2 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (45 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45

end QiushiMatmul
