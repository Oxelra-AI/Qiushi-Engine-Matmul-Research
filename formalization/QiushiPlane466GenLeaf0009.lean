import QiushiPlane466GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane466GenLeaf0009Refs : Fin 51 → RowRef 210 50 := ![.occ 16, .occ 19, .occ 25, .occ 27, .occ 28, .occ 30, .occ 31, .occ 42, .occ 65, .occ 68, .occ 69, .occ 70, .occ 74, .occ 75, .occ 76, .occ 84, .occ 100, .occ 101, .occ 104, .occ 105, .occ 111, .occ 113, .occ 120, .occ 132, .occ 136, .occ 158, .occ 172, .occ 173, .occ 176, .occ 182, .occ 186, .occ 188, .occ 192, .occ 195, .occ 198, .occ 207, .sumGe, .nonneg 0, .nonneg 14, .nonneg 18, .nonneg 31, .nonneg 32, .nonneg 35, .nonneg 41, .nonneg 43, .nonneg 44, .nonneg 46, .nonneg 48, .nonneg 49, .branchGe 24 (1), .branchGe 28 (1)]

def plane466GenLeaf0009Mult : Fin 51 → Nat := ![97, 91, 78, 22, 12, 84, 24, 4, 16, 16, 24, 14, 26, 12, 14, 18, 7, 3, 99, 103, 48, 4, 62, 34, 42, 45, 15, 46, 4, 14, 2, 13, 18, 50, 31, 2, 110, 24, 41, 103, 2, 37, 7, 60, 62, 72, 170, 17, 37, 458, 592]

theorem plane466GenLeaf0009 (x : Fin 50 → Int)
    (hroot : plane466GenOccSys.RootHolds x)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_28 : (1 : Int) ≤ x 28)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane466GenLeaf0009Refs i).resolveCoeff plane466GenOccSys j)
    (fun i => (plane466GenLeaf0009Refs i).resolveRhs plane466GenOccSys) plane466GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane466GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 16
  · exact hroot.hOcc 19
  · exact hroot.hOcc 25
  · exact hroot.hOcc 27
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 42
  · exact hroot.hOcc 65
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 84
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 111
  · exact hroot.hOcc 113
  · exact hroot.hOcc 120
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 158
  · exact hroot.hOcc 172
  · exact hroot.hOcc 173
  · exact hroot.hOcc 176
  · exact hroot.hOcc 182
  · exact hroot.hOcc 186
  · exact hroot.hOcc 188
  · exact hroot.hOcc 192
  · exact hroot.hOcc 195
  · exact hroot.hOcc 198
  · exact hroot.hOcc 207
  · change (∑ j, (-1 : Int) * x j) ≤ -plane466GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (14 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (18 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (31 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (41 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (43 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (44 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (46 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (48 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (49 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (24 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (28 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
