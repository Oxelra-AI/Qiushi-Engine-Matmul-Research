import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0002Refs : Fin 49 → RowRef 237 50 := ![.occ 7, .occ 8, .occ 9, .occ 21, .occ 22, .occ 24, .occ 25, .occ 28, .occ 34, .occ 42, .occ 54, .occ 56, .occ 103, .occ 120, .occ 139, .occ 157, .occ 158, .occ 161, .occ 163, .occ 173, .occ 174, .occ 178, .occ 180, .occ 182, .occ 192, .occ 193, .occ 194, .occ 195, .occ 203, .occ 204, .occ 214, .occ 215, .occ 229, .occ 234, .occ 236, .sumGe, .nonneg 7, .nonneg 17, .nonneg 24, .nonneg 26, .nonneg 31, .nonneg 35, .nonneg 38, .nonneg 43, .nonneg 44, .nonneg 49, .branchLe 15 (0), .branchLe 45 (0), .branchGe 18 (1)]

def plane427GenLeaf0002Mult : Fin 49 → Nat := ![104, 255, 271, 125, 195, 85, 88, 112, 210, 95, 305, 95, 70, 75, 115, 28, 47, 138, 49, 94, 41, 138, 14, 20, 18, 150, 27, 10, 86, 192, 147, 121, 158, 65, 52, 530, 18, 295, 175, 72, 228, 133, 167, 75, 107, 133, 455, 510, 1300]

theorem plane427GenLeaf0002 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_45 : x 45 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0002Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0002Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 28
  · exact hroot.hOcc 34
  · exact hroot.hOcc 42
  · exact hroot.hOcc 54
  · exact hroot.hOcc 56
  · exact hroot.hOcc 103
  · exact hroot.hOcc 120
  · exact hroot.hOcc 139
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 178
  · exact hroot.hOcc 180
  · exact hroot.hOcc 182
  · exact hroot.hOcc 192
  · exact hroot.hOcc 193
  · exact hroot.hOcc 194
  · exact hroot.hOcc 195
  · exact hroot.hOcc 203
  · exact hroot.hOcc 204
  · exact hroot.hOcc 214
  · exact hroot.hOcc 215
  · exact hroot.hOcc 229
  · exact hroot.hOcc 234
  · exact hroot.hOcc 236
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (17 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (24 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (31 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (38 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (43 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (44 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (49 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (15 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (45 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45
  · change (∑ k, (if k = (18 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
