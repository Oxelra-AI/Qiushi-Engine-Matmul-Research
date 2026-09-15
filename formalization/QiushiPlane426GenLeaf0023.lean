import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0023Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 36, .occ 50, .occ 67, .occ 71, .occ 72, .occ 81, .occ 84, .occ 99, .occ 102, .occ 103, .occ 109, .occ 113, .occ 116, .occ 117, .occ 119, .occ 121, .occ 122, .occ 128, .occ 142, .occ 176, .occ 179, .occ 181, .occ 205, .occ 223, .occ 232, .occ 235, .occ 242, .occ 258, .occ 273, .occ 275, .occ 280, .occ 282, .occ 299, .occ 323, .occ 332, .occ 334, .sumGe, .nonneg 5, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 25, .nonneg 26, .nonneg 28, .nonneg 30, .nonneg 33, .nonneg 36, .nonneg 39, .nonneg 47, .nonneg 52, .nonneg 57, .branchLe 43 (0), .branchGe 14 (1), .branchLe 42 (0), .branchLe 18 (0), .branchLe 56 (0), .branchGe 11 (1), .branchGe 49 (1)]

def plane426GenLeaf0023Mult : Fin 59 → Nat := ![438, 576, 80, 265, 371, 260, 128, 335, 159, 229, 52, 300, 56, 108, 191, 231, 81, 237, 263, 121, 133, 54, 21, 176, 110, 121, 227, 115, 68, 150, 233, 105, 135, 5, 28, 12, 102, 706, 562, 725, 620, 27, 338, 167, 100, 86, 78, 257, 146, 365, 379, 47, 551, 1099, 249, 604, 505, 1507, 1938]

theorem plane426GenLeaf0023 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_49 : (1 : Int) ≤ x 49)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_56 : x 56 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0023Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0023Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0023Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0023Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 36
  · exact hroot.hOcc 50
  · exact hroot.hOcc 67
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 99
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 142
  · exact hroot.hOcc 176
  · exact hroot.hOcc 179
  · exact hroot.hOcc 181
  · exact hroot.hOcc 205
  · exact hroot.hOcc 223
  · exact hroot.hOcc 232
  · exact hroot.hOcc 235
  · exact hroot.hOcc 242
  · exact hroot.hOcc 258
  · exact hroot.hOcc 273
  · exact hroot.hOcc 275
  · exact hroot.hOcc 280
  · exact hroot.hOcc 282
  · exact hroot.hOcc 299
  · exact hroot.hOcc 323
  · exact hroot.hOcc 332
  · exact hroot.hOcc 334
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (30 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (39 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (52 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (57 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (42 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (18 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (56 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_56
  · change (∑ k, (if k = (11 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (49 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_49

end QiushiMatmul
