import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0011Refs : Fin 43 → RowRef 237 50 := ![.occ 9, .occ 10, .occ 18, .occ 53, .occ 59, .occ 85, .occ 86, .occ 87, .occ 89, .occ 90, .occ 96, .occ 131, .occ 133, .occ 165, .occ 168, .occ 170, .occ 171, .occ 173, .occ 174, .occ 175, .occ 176, .occ 195, .occ 199, .occ 211, .occ 221, .occ 228, .occ 235, .sumGe, .nonneg 4, .nonneg 9, .nonneg 20, .nonneg 29, .nonneg 30, .nonneg 32, .nonneg 36, .nonneg 38, .nonneg 41, .nonneg 44, .nonneg 49, .branchLe 26 (0), .branchGe 15 (1), .branchLe 35 (0), .branchGe 47 (1)]

def plane427GenLeaf0011Mult : Fin 43 → Nat := ![32, 27, 3, 24, 3, 1, 5, 14, 10, 10, 2, 14, 2, 2, 1, 17, 5, 5, 9, 3, 25, 10, 13, 15, 18, 7, 2, 34, 26, 2, 45, 3, 3, 5, 2, 17, 9, 34, 1, 34, 92, 33, 93]

theorem plane427GenLeaf0011 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_47 : (1 : Int) ≤ x 47)
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0011Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0011Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 18
  · exact hroot.hOcc 53
  · exact hroot.hOcc 59
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 96
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 165
  · exact hroot.hOcc 168
  · exact hroot.hOcc 170
  · exact hroot.hOcc 171
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 195
  · exact hroot.hOcc 199
  · exact hroot.hOcc 211
  · exact hroot.hOcc 221
  · exact hroot.hOcc 228
  · exact hroot.hOcc 235
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (9 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (20 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (30 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (36 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (38 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (41 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (44 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (49 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (26 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (15 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (47 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_47

end QiushiMatmul
