import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0016Refs : Fin 51 → RowRef 237 50 := ![.occ 7, .occ 8, .occ 14, .occ 16, .occ 19, .occ 24, .occ 27, .occ 35, .occ 39, .occ 47, .occ 64, .occ 66, .occ 71, .occ 97, .occ 98, .occ 138, .occ 141, .occ 142, .occ 149, .occ 158, .occ 163, .occ 165, .occ 174, .occ 177, .occ 181, .occ 186, .occ 189, .occ 194, .occ 196, .occ 203, .occ 205, .occ 206, .occ 207, .occ 216, .occ 225, .occ 235, .sumGe, .nonneg 9, .nonneg 13, .nonneg 21, .nonneg 25, .nonneg 29, .nonneg 33, .nonneg 36, .nonneg 38, .nonneg 39, .nonneg 43, .nonneg 46, .branchGe 26 (1), .branchGe 14 (1), .branchLe 18 (0)]

def plane427GenLeaf0016Mult : Fin 51 → Nat := ![191, 39, 9, 25, 142, 36, 49, 76, 97, 67, 64, 32, 27, 73, 43, 14, 4, 4, 81, 88, 59, 96, 90, 65, 77, 2, 38, 105, 59, 27, 29, 30, 4, 4, 44, 58, 276, 258, 121, 189, 5, 97, 27, 43, 59, 32, 70, 15, 292, 522, 217]

theorem plane427GenLeaf0016 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_18 : x 18 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0016Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0016Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0016Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0016Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 14
  · exact hroot.hOcc 16
  · exact hroot.hOcc 19
  · exact hroot.hOcc 24
  · exact hroot.hOcc 27
  · exact hroot.hOcc 35
  · exact hroot.hOcc 39
  · exact hroot.hOcc 47
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 71
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 138
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 149
  · exact hroot.hOcc 158
  · exact hroot.hOcc 163
  · exact hroot.hOcc 165
  · exact hroot.hOcc 174
  · exact hroot.hOcc 177
  · exact hroot.hOcc 181
  · exact hroot.hOcc 186
  · exact hroot.hOcc 189
  · exact hroot.hOcc 194
  · exact hroot.hOcc 196
  · exact hroot.hOcc 203
  · exact hroot.hOcc 205
  · exact hroot.hOcc 206
  · exact hroot.hOcc 207
  · exact hroot.hOcc 216
  · exact hroot.hOcc 225
  · exact hroot.hOcc 235
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (13 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (21 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (25 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (33 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (38 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (39 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (43 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (46 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (26 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (18 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18

end QiushiMatmul
