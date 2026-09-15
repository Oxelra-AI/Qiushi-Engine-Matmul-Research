import QiushiPlane464GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane464GenLeaf0006Refs : Fin 51 → RowRef 202 50 := ![.occ 20, .occ 33, .occ 46, .occ 54, .occ 59, .occ 60, .occ 62, .occ 67, .occ 68, .occ 75, .occ 79, .occ 81, .occ 86, .occ 93, .occ 94, .occ 98, .occ 100, .occ 101, .occ 104, .occ 112, .occ 133, .occ 134, .occ 139, .occ 141, .occ 143, .occ 149, .occ 150, .occ 158, .occ 160, .occ 162, .occ 172, .occ 174, .occ 186, .occ 187, .occ 189, .occ 190, .occ 191, .occ 192, .occ 197, .sumGe, .nonneg 0, .nonneg 7, .nonneg 13, .nonneg 32, .nonneg 33, .nonneg 36, .nonneg 46, .branchGe 1 (1), .branchLe 49 (0), .branchLe 40 (0), .branchGe 19 (1)]

def plane464GenLeaf0006Mult : Fin 51 → Nat := ![2682, 3562, 2508, 2848, 4960, 432, 668, 12236, 1666, 1620, 196, 1516, 2288, 1988, 2034, 1896, 1994, 992, 4994, 4694, 1620, 648, 4252, 2314, 306, 562, 492, 204, 1368, 582, 4422, 2006, 1017, 2477, 108, 4947, 1621, 2530, 2094, 14982, 2744, 3288, 5428, 5528, 4482, 5422, 264, 20220, 7894, 14874, 47136]

theorem plane464GenLeaf0006 (x : Fin 50 → Int)
    (hroot : plane464GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hUB_49 : x 49 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane464GenLeaf0006Refs i).resolveCoeff plane464GenOccSys j)
    (fun i => (plane464GenLeaf0006Refs i).resolveRhs plane464GenOccSys) plane464GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane464GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 20
  · exact hroot.hOcc 33
  · exact hroot.hOcc 46
  · exact hroot.hOcc 54
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 62
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 75
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 86
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 104
  · exact hroot.hOcc 112
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 149
  · exact hroot.hOcc 150
  · exact hroot.hOcc 158
  · exact hroot.hOcc 160
  · exact hroot.hOcc 162
  · exact hroot.hOcc 172
  · exact hroot.hOcc 174
  · exact hroot.hOcc 186
  · exact hroot.hOcc 187
  · exact hroot.hOcc 189
  · exact hroot.hOcc 190
  · exact hroot.hOcc 191
  · exact hroot.hOcc 192
  · exact hroot.hOcc 197
  · change (∑ j, (-1 : Int) * x j) ≤ -plane464GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (13 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (46 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (1 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (49 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_49
  · change (∑ k, (if k = (40 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (19 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19

end QiushiMatmul
