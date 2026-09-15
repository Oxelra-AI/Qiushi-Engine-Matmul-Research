import QiushiPlane457GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane457GenLeaf0003Refs : Fin 50 → RowRef 178 49 := ![.occ 18, .occ 20, .occ 21, .occ 27, .occ 29, .occ 39, .occ 41, .occ 47, .occ 59, .occ 64, .occ 67, .occ 68, .occ 69, .occ 70, .occ 71, .occ 74, .occ 75, .occ 78, .occ 80, .occ 85, .occ 91, .occ 94, .occ 95, .occ 97, .occ 98, .occ 112, .occ 120, .occ 126, .occ 130, .occ 131, .occ 143, .occ 151, .occ 152, .occ 154, .occ 155, .occ 171, .occ 176, .occ 177, .sumGe, .nonneg 6, .nonneg 8, .nonneg 11, .nonneg 27, .nonneg 33, .nonneg 47, .nonneg 48, .branchGe 3 (1), .branchLe 23 (0), .branchLe 26 (0), .branchLe 35 (0)]

def plane457GenLeaf0003Mult : Fin 50 → Nat := ![1234, 2744, 2395, 221, 512, 661, 3650, 4966, 14172, 5447, 4172, 5518, 12378, 5167, 3994, 9175, 5263, 1492, 75, 706, 7211, 766, 974, 1766, 11193, 1906, 4263, 6273, 1061, 817, 4017, 6512, 128, 425, 1865, 2868, 140, 351, 15939, 4825, 4173, 6114, 6783, 2492, 2011, 1797, 55351, 9526, 15588, 14033]

theorem plane457GenLeaf0003 (x : Fin 49 → Int)
    (hroot : plane457GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane457GenLeaf0003Refs i).resolveCoeff plane457GenOccSys j)
    (fun i => (plane457GenLeaf0003Refs i).resolveRhs plane457GenOccSys) plane457GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane457GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 18
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 27
  · exact hroot.hOcc 29
  · exact hroot.hOcc 39
  · exact hroot.hOcc 41
  · exact hroot.hOcc 47
  · exact hroot.hOcc 59
  · exact hroot.hOcc 64
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 85
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 112
  · exact hroot.hOcc 120
  · exact hroot.hOcc 126
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 143
  · exact hroot.hOcc 151
  · exact hroot.hOcc 152
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 171
  · exact hroot.hOcc 176
  · exact hroot.hOcc 177
  · change (∑ j, (-1 : Int) * x j) ≤ -plane457GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (8 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (47 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (48 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (3 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (35 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35

end QiushiMatmul
