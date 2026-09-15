import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0025Refs : Fin 59 → RowRef 340 58 := ![.occ 8, .occ 24, .occ 63, .occ 68, .occ 79, .occ 81, .occ 84, .occ 86, .occ 89, .occ 102, .occ 103, .occ 104, .occ 113, .occ 117, .occ 121, .occ 122, .occ 131, .occ 142, .occ 147, .occ 149, .occ 155, .occ 164, .occ 187, .occ 205, .occ 208, .occ 215, .occ 219, .occ 227, .occ 239, .occ 251, .occ 252, .occ 258, .occ 265, .occ 278, .occ 290, .occ 294, .occ 317, .occ 325, .occ 334, .sumGe, .nonneg 5, .nonneg 16, .nonneg 17, .nonneg 25, .nonneg 26, .nonneg 28, .nonneg 32, .nonneg 36, .nonneg 40, .nonneg 50, .nonneg 52, .nonneg 54, .branchLe 43 (0), .branchGe 14 (1), .branchLe 42 (0), .branchGe 18 (1), .branchLe 49 (0), .branchLe 27 (0), .branchLe 35 (0)]

def plane426GenLeaf0025Mult : Fin 59 → Nat := ![13326, 7873, 404, 54, 3755, 3616, 3957, 8537, 3130, 1140, 894, 1663, 1530, 4031, 6628, 6371, 7713, 6123, 1655, 1053, 1999, 4514, 3378, 3822, 1604, 509, 4453, 5074, 558, 591, 48, 3000, 288, 2173, 2960, 768, 690, 3663, 1437, 16802, 5281, 25144, 17580, 1958, 5546, 7131, 1371, 11045, 422, 5075, 3406, 404, 16244, 14597, 5916, 32566, 11654, 15147, 13139]

theorem plane426GenLeaf0025 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_49 : x 49 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0025Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0025Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0025Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0025Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 24
  · exact hroot.hOcc 63
  · exact hroot.hOcc 68
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 89
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 113
  · exact hroot.hOcc 117
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 131
  · exact hroot.hOcc 142
  · exact hroot.hOcc 147
  · exact hroot.hOcc 149
  · exact hroot.hOcc 155
  · exact hroot.hOcc 164
  · exact hroot.hOcc 187
  · exact hroot.hOcc 205
  · exact hroot.hOcc 208
  · exact hroot.hOcc 215
  · exact hroot.hOcc 219
  · exact hroot.hOcc 227
  · exact hroot.hOcc 239
  · exact hroot.hOcc 251
  · exact hroot.hOcc 252
  · exact hroot.hOcc 258
  · exact hroot.hOcc 265
  · exact hroot.hOcc 278
  · exact hroot.hOcc 290
  · exact hroot.hOcc 294
  · exact hroot.hOcc 317
  · exact hroot.hOcc 325
  · exact hroot.hOcc 334
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (32 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (40 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (54 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (42 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (18 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (49 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_49
  · change (∑ k, (if k = (27 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (35 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35

end QiushiMatmul
