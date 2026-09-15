import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0014Refs : Fin 63 → RowRef 294 62 := ![.occ 14, .occ 23, .occ 30, .occ 38, .occ 46, .occ 47, .occ 62, .occ 65, .occ 67, .occ 68, .occ 71, .occ 73, .occ 74, .occ 77, .occ 78, .occ 80, .occ 83, .occ 84, .occ 85, .occ 89, .occ 94, .occ 96, .occ 97, .occ 99, .occ 102, .occ 105, .occ 106, .occ 120, .occ 163, .occ 174, .occ 175, .occ 181, .occ 193, .occ 194, .occ 222, .occ 233, .occ 244, .occ 260, .occ 261, .occ 271, .occ 279, .occ 282, .occ 285, .occ 286, .occ 292, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 10, .nonneg 13, .nonneg 20, .nonneg 38, .nonneg 39, .nonneg 41, .nonneg 47, .nonneg 48, .nonneg 53, .nonneg 59, .branchGe 5 (1), .branchGe 24 (1), .branchLe 27 (0), .branchGe 34 (2)]

def plane462GenLeaf0014Mult : Fin 63 → Nat := ![8785, 11422, 2178, 11056, 9110, 10662, 12154, 13802, 4964, 23815, 18152, 3522, 12727, 8044, 30223, 15576, 2470, 29312, 4872, 1688, 15000, 6306, 12819, 17239, 7601, 15832, 3090, 320, 5934, 7631, 19799, 5674, 11032, 2238, 390, 15996, 3148, 13108, 5082, 11433, 14769, 326, 4129, 1984, 15720, 66872, 79538, 84090, 25864, 6078, 18272, 5556, 22346, 22294, 19456, 36358, 71862, 27790, 18826, 28322, 70824, 66872, 131132]

theorem plane462GenLeaf0014 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_34 : (2 : Int) ≤ x 34)
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0014Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0014Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0014Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0014Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 23
  · exact hroot.hOcc 30
  · exact hroot.hOcc 38
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 62
  · exact hroot.hOcc 65
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 71
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 94
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 99
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 120
  · exact hroot.hOcc 163
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 181
  · exact hroot.hOcc 193
  · exact hroot.hOcc 194
  · exact hroot.hOcc 222
  · exact hroot.hOcc 233
  · exact hroot.hOcc 244
  · exact hroot.hOcc 260
  · exact hroot.hOcc 261
  · exact hroot.hOcc 271
  · exact hroot.hOcc 279
  · exact hroot.hOcc 282
  · exact hroot.hOcc 285
  · exact hroot.hOcc 286
  · exact hroot.hOcc 292
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (13 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (38 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (41 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (47 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (48 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (5 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (24 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (27 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (34 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34

end QiushiMatmul
