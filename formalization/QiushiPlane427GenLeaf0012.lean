import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0012Refs : Fin 47 → RowRef 237 50 := ![.occ 9, .occ 17, .occ 25, .occ 26, .occ 45, .occ 47, .occ 48, .occ 49, .occ 59, .occ 63, .occ 66, .occ 70, .occ 84, .occ 130, .occ 145, .occ 148, .occ 149, .occ 153, .occ 157, .occ 158, .occ 168, .occ 170, .occ 173, .occ 176, .occ 196, .occ 201, .occ 206, .occ 208, .occ 209, .occ 210, .occ 211, .occ 215, .sumGe, .nonneg 2, .nonneg 4, .nonneg 9, .nonneg 12, .nonneg 20, .nonneg 25, .nonneg 26, .nonneg 27, .nonneg 29, .nonneg 31, .nonneg 40, .nonneg 49, .branchGe 15 (1), .branchGe 35 (1)]

def plane427GenLeaf0012Mult : Fin 47 → Nat := ![30, 4, 6, 20, 10, 14, 2, 24, 6, 16, 6, 4, 2, 3, 9, 13, 2, 5, 11, 4, 3, 6, 7, 12, 19, 17, 9, 6, 4, 2, 5, 7, 36, 8, 10, 18, 42, 6, 12, 6, 12, 12, 18, 12, 6, 54, 72]

theorem plane427GenLeaf0012 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0012Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0012Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0012Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0012Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 9
  · exact hroot.hOcc 17
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 45
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 59
  · exact hroot.hOcc 63
  · exact hroot.hOcc 66
  · exact hroot.hOcc 70
  · exact hroot.hOcc 84
  · exact hroot.hOcc 130
  · exact hroot.hOcc 145
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 153
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 168
  · exact hroot.hOcc 170
  · exact hroot.hOcc 173
  · exact hroot.hOcc 176
  · exact hroot.hOcc 196
  · exact hroot.hOcc 201
  · exact hroot.hOcc 206
  · exact hroot.hOcc 208
  · exact hroot.hOcc 209
  · exact hroot.hOcc 210
  · exact hroot.hOcc 211
  · exact hroot.hOcc 215
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (4 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (9 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (12 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (20 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (25 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (27 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (31 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (40 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (49 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (15 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
