import QiushiPlane427GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane427GenLeaf0017Refs : Fin 50 → RowRef 237 50 := ![.occ 7, .occ 15, .occ 28, .occ 29, .occ 34, .occ 39, .occ 40, .occ 63, .occ 64, .occ 66, .occ 132, .occ 134, .occ 138, .occ 145, .occ 157, .occ 158, .occ 161, .occ 163, .occ 165, .occ 167, .occ 168, .occ 173, .occ 174, .occ 181, .occ 182, .occ 189, .occ 195, .occ 196, .occ 198, .occ 204, .occ 205, .occ 206, .occ 211, .occ 229, .sumGe, .nonneg 4, .nonneg 5, .nonneg 21, .nonneg 31, .nonneg 35, .nonneg 36, .nonneg 38, .nonneg 39, .nonneg 40, .nonneg 43, .nonneg 44, .nonneg 46, .branchGe 26 (1), .branchGe 14 (1), .branchGe 18 (1)]

def plane427GenLeaf0017Mult : Fin 50 → Nat := ![1038, 40, 306, 542, 96, 482, 224, 300, 140, 354, 244, 225, 147, 492, 312, 609, 920, 59, 10, 93, 5, 82, 115, 174, 198, 61, 68, 658, 104, 316, 124, 52, 258, 204, 1242, 896, 170, 80, 522, 338, 184, 1968, 128, 258, 98, 424, 766, 2178, 522, 2382]

theorem plane427GenLeaf0017 (x : Fin 50 → Int)
    (hroot : plane427GenOccSys.RootHolds x)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_18 : (1 : Int) ≤ x 18)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane427GenLeaf0017Refs i).resolveCoeff plane427GenOccSys j)
    (fun i => (plane427GenLeaf0017Refs i).resolveRhs plane427GenOccSys) plane427GenLeaf0017Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane427GenLeaf0017Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 15
  · exact hroot.hOcc 28
  · exact hroot.hOcc 29
  · exact hroot.hOcc 34
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 138
  · exact hroot.hOcc 145
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 161
  · exact hroot.hOcc 163
  · exact hroot.hOcc 165
  · exact hroot.hOcc 167
  · exact hroot.hOcc 168
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 181
  · exact hroot.hOcc 182
  · exact hroot.hOcc 189
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 198
  · exact hroot.hOcc 204
  · exact hroot.hOcc 205
  · exact hroot.hOcc 206
  · exact hroot.hOcc 211
  · exact hroot.hOcc 229
  · change (∑ j, (-1 : Int) * x j) ≤ -plane427GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (5 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (21 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (31 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (36 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (38 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (39 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (43 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (44 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (46 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (26 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (18 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
