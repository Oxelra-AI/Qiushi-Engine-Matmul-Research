import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0015Refs : Fin 50 → RowRef 237 50 := ![.occ 6, .occ 7, .occ 8, .occ 29, .occ 31, .occ 39, .occ 41, .occ 71, .occ 82, .occ 92, .occ 93, .occ 94, .occ 95, .occ 118, .occ 129, .occ 135, .occ 137, .occ 139, .occ 141, .occ 144, .occ 163, .occ 166, .occ 182, .occ 184, .occ 187, .occ 189, .occ 190, .occ 192, .occ 195, .occ 196, .occ 201, .occ 205, .occ 222, .occ 223, .sumGe, .nonneg 5, .nonneg 7, .nonneg 9, .nonneg 12, .nonneg 13, .nonneg 15, .nonneg 16, .nonneg 17, .nonneg 18, .nonneg 25, .nonneg 33, .nonneg 41, .branchGe 26 (1), .branchLe 14 (0), .branchGe 48 (1)]

def plane427GenLeaf0015Mult : Fin 50 → Nat := ![13, 14, 26, 7, 4, 3, 15, 21, 6, 7, 3, 5, 1, 1, 4, 8, 4, 7, 6, 12, 6, 12, 13, 1, 8, 11, 9, 7, 3, 3, 15, 7, 1, 3, 29, 13, 7, 12, 24, 1, 3, 21, 13, 8, 28, 7, 5, 82, 23, 66]

theorem plane427GenLeaf0015 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_48 : (1 : Int) ≤ x 48)
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0015Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0015Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0015Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0015Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 29
  · exact hroot.hOcc 31
  · exact hroot.hOcc 39
  · exact hroot.hOcc 41
  · exact hroot.hOcc 71
  · exact hroot.hOcc 82
  · exact hroot.hOcc 92
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 118
  · exact hroot.hOcc 129
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 144
  · exact hroot.hOcc 163
  · exact hroot.hOcc 166
  · exact hroot.hOcc 182
  · exact hroot.hOcc 184
  · exact hroot.hOcc 187
  · exact hroot.hOcc 189
  · exact hroot.hOcc 190
  · exact hroot.hOcc 192
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 201
  · exact hroot.hOcc 205
  · exact hroot.hOcc 222
  · exact hroot.hOcc 223
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (7 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (9 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (12 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (13 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (15 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (16 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (18 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (25 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (33 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (41 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (26 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (48 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_48

end QiushiMatmul
