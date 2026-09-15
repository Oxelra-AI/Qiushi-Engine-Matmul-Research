import QiushiPlane453GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane453GenLeaf0008Refs : Fin 40 → RowRef 210 50 := ![.occ 25, .occ 28, .occ 37, .occ 66, .occ 68, .occ 72, .occ 73, .occ 75, .occ 78, .occ 103, .occ 105, .occ 106, .occ 108, .occ 110, .occ 120, .occ 127, .occ 129, .occ 132, .occ 135, .occ 149, .occ 166, .occ 172, .occ 176, .occ 177, .occ 182, .occ 193, .occ 198, .occ 201, .sumGe, .nonneg 0, .nonneg 23, .nonneg 25, .nonneg 31, .nonneg 45, .nonneg 48, .branchLe 35 (0), .branchGe 5 (2), .branchLe 41 (0), .branchLe 1 (0), .branchGe 27 (1)]

def plane453GenLeaf0008Mult : Fin 40 → Nat := ![14, 6, 2, 1, 1, 4, 2, 10, 4, 10, 10, 1, 7, 1, 12, 17, 1, 11, 1, 1, 9, 3, 3, 3, 10, 4, 6, 1, 20, 3, 12, 27, 14, 36, 10, 18, 30, 18, 12, 109]

theorem plane453GenLeaf0008 (x : Fin 50 → Int)
    (hroot : plane453GenOccSys.RootHolds x)
    (hLB_5 : (2 : Int) ≤ x 5)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane453GenLeaf0008Refs i).resolveCoeff plane453GenOccSys j)
    (fun i => (plane453GenLeaf0008Refs i).resolveRhs plane453GenOccSys) plane453GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane453GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 25
  · exact hroot.hOcc 28
  · exact hroot.hOcc 37
  · exact hroot.hOcc 66
  · exact hroot.hOcc 68
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 75
  · exact hroot.hOcc 78
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 120
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 135
  · exact hroot.hOcc 149
  · exact hroot.hOcc 166
  · exact hroot.hOcc 172
  · exact hroot.hOcc 176
  · exact hroot.hOcc 177
  · exact hroot.hOcc 182
  · exact hroot.hOcc 193
  · exact hroot.hOcc 198
  · exact hroot.hOcc 201
  · change (∑ j, (-1 : Int) * x j) ≤ -plane453GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (23 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (25 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (31 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (45 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (48 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (41 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (1 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (27 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27

end QiushiMatmul
