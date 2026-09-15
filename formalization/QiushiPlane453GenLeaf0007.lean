import QiushiPlane453GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane453GenLeaf0007Refs : Fin 45 → RowRef 210 50 := ![.occ 29, .occ 30, .occ 33, .occ 38, .occ 39, .occ 47, .occ 59, .occ 66, .occ 67, .occ 68, .occ 70, .occ 72, .occ 73, .occ 81, .occ 85, .occ 106, .occ 107, .occ 128, .occ 130, .occ 166, .occ 167, .occ 168, .occ 169, .occ 170, .occ 172, .occ 182, .occ 199, .occ 200, .sumGe, .nonneg 0, .nonneg 22, .nonneg 23, .nonneg 25, .nonneg 28, .nonneg 29, .nonneg 31, .nonneg 44, .nonneg 45, .nonneg 47, .branchLe 35 (0), .branchGe 5 (2), .branchLe 41 (0), .branchLe 1 (0), .branchLe 27 (0), .branchGe 49 (1)]

def plane453GenLeaf0007Mult : Fin 45 → Nat := ![5, 10, 7, 5, 10, 7, 26, 7, 3, 7, 3, 27, 20, 3, 3, 24, 15, 2, 2, 8, 9, 13, 13, 13, 7, 11, 4, 9, 33, 20, 6, 20, 26, 26, 7, 61, 4, 5, 9, 20, 71, 20, 13, 10, 108]

theorem plane453GenLeaf0007 (x : Fin 50 → Int)
    (hroot : plane453GenOccSys.RootHolds x)
    (hLB_5 : (2 : Int) ≤ x 5)
    (hLB_49 : (1 : Int) ≤ x 49)
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane453GenLeaf0007Refs i).resolveCoeff plane453GenOccSys j)
    (fun i => (plane453GenLeaf0007Refs i).resolveRhs plane453GenOccSys) plane453GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane453GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 33
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 47
  · exact hroot.hOcc 59
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 70
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 166
  · exact hroot.hOcc 167
  · exact hroot.hOcc 168
  · exact hroot.hOcc 169
  · exact hroot.hOcc 170
  · exact hroot.hOcc 172
  · exact hroot.hOcc 182
  · exact hroot.hOcc 199
  · exact hroot.hOcc 200
  · change (∑ j, (-1 : Int) * x j) ≤ -plane453GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (22 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (25 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (28 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (31 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (44 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (45 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (47 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (41 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (1 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (27 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (49 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_49

end QiushiMatmul
