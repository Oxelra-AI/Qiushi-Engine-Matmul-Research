import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0034Refs : Fin 58 → RowRef 340 58 := ![.occ 5, .occ 16, .occ 20, .occ 31, .occ 41, .occ 57, .occ 61, .occ 62, .occ 84, .occ 86, .occ 88, .occ 92, .occ 93, .occ 99, .occ 104, .occ 113, .occ 117, .occ 118, .occ 121, .occ 123, .occ 124, .occ 131, .occ 135, .occ 138, .occ 139, .occ 151, .occ 153, .occ 159, .occ 161, .occ 167, .occ 168, .occ 175, .occ 184, .occ 188, .occ 198, .occ 217, .occ 251, .occ 283, .occ 284, .occ 285, .occ 295, .occ 299, .occ 309, .occ 316, .sumGe, .nonneg 16, .nonneg 17, .nonneg 22, .nonneg 25, .nonneg 26, .nonneg 33, .nonneg 46, .nonneg 50, .nonneg 53, .branchGe 43 (1), .branchGe 34 (1), .branchLe 49 (0), .branchLe 11 (0)]

def plane426GenLeaf0034Mult : Fin 58 → Nat := ![298, 118, 6521, 2543, 4343, 1188, 1053, 357, 2775, 1023, 929, 778, 1090, 4279, 151, 165, 1107, 654, 2366, 14, 1720, 354, 4773, 4790, 890, 318, 501, 786, 944, 293, 1268, 4332, 3039, 2036, 329, 123, 669, 561, 151, 1503, 2432, 17, 1308, 3585, 7205, 7706, 18921, 506, 2992, 1137, 4129, 27, 2206, 2898, 39647, 1170, 4166, 5169]

theorem plane426GenLeaf0034 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_49 : x 49 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0034Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0034Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0034Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0034Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 16
  · exact hroot.hOcc 20
  · exact hroot.hOcc 31
  · exact hroot.hOcc 41
  · exact hroot.hOcc 57
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 92
  · exact hroot.hOcc 93
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 113
  · exact hroot.hOcc 117
  · exact hroot.hOcc 118
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 131
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 151
  · exact hroot.hOcc 153
  · exact hroot.hOcc 159
  · exact hroot.hOcc 161
  · exact hroot.hOcc 167
  · exact hroot.hOcc 168
  · exact hroot.hOcc 175
  · exact hroot.hOcc 184
  · exact hroot.hOcc 188
  · exact hroot.hOcc 198
  · exact hroot.hOcc 217
  · exact hroot.hOcc 251
  · exact hroot.hOcc 283
  · exact hroot.hOcc 284
  · exact hroot.hOcc 285
  · exact hroot.hOcc 295
  · exact hroot.hOcc 299
  · exact hroot.hOcc 309
  · exact hroot.hOcc 316
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (22 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (46 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (53 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (43 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (34 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (49 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_49
  · change (∑ k, (if k = (11 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11

end QiushiMatmul
