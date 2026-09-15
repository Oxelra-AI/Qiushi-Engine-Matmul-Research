import QiushiPlane466GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane466GenLeaf0007Refs : Fin 51 → RowRef 210 50 := ![.occ 37, .occ 44, .occ 63, .occ 68, .occ 77, .occ 80, .occ 82, .occ 89, .occ 90, .occ 96, .occ 101, .occ 102, .occ 103, .occ 108, .occ 109, .occ 113, .occ 114, .occ 115, .occ 116, .occ 147, .occ 149, .occ 155, .occ 159, .occ 167, .occ 168, .occ 172, .occ 173, .occ 188, .occ 195, .occ 201, .occ 202, .occ 203, .occ 207, .sumGe, .nonneg 0, .nonneg 15, .nonneg 17, .nonneg 18, .nonneg 22, .nonneg 29, .nonneg 32, .nonneg 34, .nonneg 36, .nonneg 37, .nonneg 39, .nonneg 41, .nonneg 43, .nonneg 44, .branchLe 24 (0), .branchGe 19 (1), .branchGe 30 (2)]

def plane466GenLeaf0007Mult : Fin 51 → Nat := ![46, 33, 13, 36, 51, 4, 2, 40, 88, 85, 64, 26, 2, 15, 97, 12, 19, 48, 116, 99, 5, 56, 60, 42, 32, 26, 5, 109, 54, 5, 24, 4, 1, 164, 99, 27, 136, 15, 24, 55, 49, 36, 11, 129, 43, 32, 36, 131, 155, 127, 720]

theorem plane466GenLeaf0007 (x : Fin 50 → Int)
    (hroot : plane466GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_30 : (2 : Int) ≤ x 30)
    (hUB_24 : x 24 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane466GenLeaf0007Refs i).resolveCoeff plane466GenOccSys j)
    (fun i => (plane466GenLeaf0007Refs i).resolveRhs plane466GenOccSys) plane466GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane466GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 37
  · exact hroot.hOcc 44
  · exact hroot.hOcc 63
  · exact hroot.hOcc 68
  · exact hroot.hOcc 77
  · exact hroot.hOcc 80
  · exact hroot.hOcc 82
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 96
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 147
  · exact hroot.hOcc 149
  · exact hroot.hOcc 155
  · exact hroot.hOcc 159
  · exact hroot.hOcc 167
  · exact hroot.hOcc 168
  · exact hroot.hOcc 172
  · exact hroot.hOcc 173
  · exact hroot.hOcc 188
  · exact hroot.hOcc 195
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 203
  · exact hroot.hOcc 207
  · change (∑ j, (-1 : Int) * x j) ≤ -plane466GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (15 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (17 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (18 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (22 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (36 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (37 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (39 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (41 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (43 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (44 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (24 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (19 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (30 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30

end QiushiMatmul
