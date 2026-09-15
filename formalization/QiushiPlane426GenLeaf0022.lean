import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0022Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 18, .occ 19, .occ 50, .occ 63, .occ 67, .occ 71, .occ 74, .occ 76, .occ 81, .occ 84, .occ 90, .occ 91, .occ 102, .occ 104, .occ 109, .occ 113, .occ 117, .occ 121, .occ 122, .occ 124, .occ 125, .occ 134, .occ 142, .occ 154, .occ 158, .occ 165, .occ 205, .occ 208, .occ 215, .occ 228, .occ 235, .occ 236, .occ 240, .occ 258, .occ 275, .occ 282, .occ 298, .occ 307, .occ 318, .occ 333, .sumGe, .nonneg 5, .nonneg 8, .nonneg 16, .nonneg 17, .nonneg 24, .nonneg 28, .nonneg 36, .nonneg 44, .nonneg 47, .nonneg 50, .branchLe 43 (0), .branchGe 14 (1), .branchLe 42 (0), .branchLe 18 (0), .branchLe 56 (0), .branchGe 11 (1), .branchLe 49 (0)]

def plane426GenLeaf0022Mult : Fin 59 → Nat := ![46169, 823, 7643, 19173, 18125, 11625, 45802, 7790, 27964, 7825, 25194, 14256, 996, 22944, 3594, 3526, 46631, 17245, 11151, 39061, 181, 8279, 6299, 40765, 16, 15424, 2248, 15498, 6298, 8692, 4149, 6668, 31935, 3099, 4620, 32613, 14690, 896, 989, 5552, 10121, 70996, 68468, 44075, 45427, 111591, 3380, 16368, 62326, 6527, 19040, 68229, 66847, 106870, 46185, 62304, 15490, 208920, 28867]

theorem plane426GenLeaf0022 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_56 : x 56 ≤ (0 : Int))
    (hUB_49 : x 49 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0022Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0022Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0022Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0022Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 50
  · exact hroot.hOcc 63
  · exact hroot.hOcc 67
  · exact hroot.hOcc 71
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 117
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 134
  · exact hroot.hOcc 142
  · exact hroot.hOcc 154
  · exact hroot.hOcc 158
  · exact hroot.hOcc 165
  · exact hroot.hOcc 205
  · exact hroot.hOcc 208
  · exact hroot.hOcc 215
  · exact hroot.hOcc 228
  · exact hroot.hOcc 235
  · exact hroot.hOcc 236
  · exact hroot.hOcc 240
  · exact hroot.hOcc 258
  · exact hroot.hOcc 275
  · exact hroot.hOcc 282
  · exact hroot.hOcc 298
  · exact hroot.hOcc 307
  · exact hroot.hOcc 318
  · exact hroot.hOcc 333
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (8 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (44 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (42 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (18 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (56 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_56
  · change (∑ k, (if k = (11 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (49 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_49

end QiushiMatmul
