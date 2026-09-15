import QiushiPlane453GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane453GenLeaf0006Refs : Fin 49 → RowRef 210 50 := ![.occ 30, .occ 33, .occ 34, .occ 39, .occ 47, .occ 48, .occ 66, .occ 67, .occ 70, .occ 72, .occ 73, .occ 75, .occ 81, .occ 85, .occ 102, .occ 104, .occ 110, .occ 111, .occ 128, .occ 129, .occ 146, .occ 153, .occ 159, .occ 160, .occ 169, .occ 170, .occ 172, .occ 185, .occ 190, .occ 192, .occ 195, .occ 202, .occ 205, .occ 206, .occ 209, .sumGe, .nonneg 0, .nonneg 22, .nonneg 23, .nonneg 24, .nonneg 28, .nonneg 29, .nonneg 47, .branchLe 35 (0), .branchGe 5 (2), .branchLe 41 (0), .branchLe 1 (0), .branchLe 27 (0), .branchLe 49 (0)]

def plane453GenLeaf0006Mult : Fin 49 → Nat := ![9, 2, 7, 17, 2, 15, 4, 26, 22, 50, 28, 17, 18, 18, 22, 22, 8, 76, 8, 27, 21, 22, 2, 2, 16, 12, 23, 48, 2, 6, 2, 35, 12, 8, 35, 108, 52, 78, 44, 27, 52, 26, 13, 66, 230, 58, 54, 108, 57]

theorem plane453GenLeaf0006 (x : Fin 50 → Int)
    (hroot : plane453GenOccSys.RootHolds x)
    (hLB_5 : (2 : Int) ≤ x 5)
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_49 : x 49 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane453GenLeaf0006Refs i).resolveCoeff plane453GenOccSys j)
    (fun i => (plane453GenLeaf0006Refs i).resolveRhs plane453GenOccSys) plane453GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane453GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 30
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 39
  · exact hroot.hOcc 47
  · exact hroot.hOcc 48
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 70
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 75
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 146
  · exact hroot.hOcc 153
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 169
  · exact hroot.hOcc 170
  · exact hroot.hOcc 172
  · exact hroot.hOcc 185
  · exact hroot.hOcc 190
  · exact hroot.hOcc 192
  · exact hroot.hOcc 195
  · exact hroot.hOcc 202
  · exact hroot.hOcc 205
  · exact hroot.hOcc 206
  · exact hroot.hOcc 209
  · change (∑ j, (-1 : Int) * x j) ≤ -plane453GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (22 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (28 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (47 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (41 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (1 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (27 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (49 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_49

end QiushiMatmul
