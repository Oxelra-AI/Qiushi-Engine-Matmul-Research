import QiushiPlane453GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane453GenLeaf0009Refs : Fin 44 → RowRef 210 50 := ![.occ 13, .occ 15, .occ 17, .occ 19, .occ 26, .occ 29, .occ 35, .occ 38, .occ 40, .occ 56, .occ 57, .occ 66, .occ 67, .occ 68, .occ 70, .occ 73, .occ 75, .occ 103, .occ 105, .occ 106, .occ 111, .occ 112, .occ 135, .occ 141, .occ 152, .occ 153, .occ 154, .occ 171, .occ 172, .occ 173, .occ 175, .occ 198, .sumGe, .nonneg 0, .nonneg 2, .nonneg 20, .nonneg 23, .nonneg 24, .nonneg 31, .nonneg 48, .branchLe 35 (0), .branchGe 5 (2), .branchLe 41 (0), .branchGe 1 (1)]

def plane453GenLeaf0009Mult : Fin 44 → Nat := ![107, 1, 107, 1, 19, 8, 19, 8, 19, 37, 24, 54, 115, 54, 115, 185, 45, 69, 69, 80, 114, 37, 18, 3, 116, 42, 54, 23, 82, 28, 46, 24, 185, 300, 153, 9, 286, 83, 45, 82, 185, 427, 185, 624]

theorem plane453GenLeaf0009 (x : Fin 50 → Int)
    (hroot : plane453GenOccSys.RootHolds x)
    (hLB_5 : (2 : Int) ≤ x 5)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane453GenLeaf0009Refs i).resolveCoeff plane453GenOccSys j)
    (fun i => (plane453GenLeaf0009Refs i).resolveRhs plane453GenOccSys) plane453GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane453GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 13
  · exact hroot.hOcc 15
  · exact hroot.hOcc 17
  · exact hroot.hOcc 19
  · exact hroot.hOcc 26
  · exact hroot.hOcc 29
  · exact hroot.hOcc 35
  · exact hroot.hOcc 38
  · exact hroot.hOcc 40
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 70
  · exact hroot.hOcc 73
  · exact hroot.hOcc 75
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 135
  · exact hroot.hOcc 141
  · exact hroot.hOcc 152
  · exact hroot.hOcc 153
  · exact hroot.hOcc 154
  · exact hroot.hOcc 171
  · exact hroot.hOcc 172
  · exact hroot.hOcc 173
  · exact hroot.hOcc 175
  · exact hroot.hOcc 198
  · change (∑ j, (-1 : Int) * x j) ≤ -plane453GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (2 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (20 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (23 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (31 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (48 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (41 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (1 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
