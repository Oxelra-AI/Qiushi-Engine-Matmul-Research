import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0021Refs : Fin 36 → RowRef 294 62 := ![.occ 37, .occ 58, .occ 68, .occ 71, .occ 73, .occ 78, .occ 81, .occ 85, .occ 88, .occ 91, .occ 97, .occ 100, .occ 103, .occ 109, .occ 165, .occ 166, .occ 167, .occ 174, .occ 175, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 10, .nonneg 12, .nonneg 15, .nonneg 17, .nonneg 19, .nonneg 23, .nonneg 25, .nonneg 29, .branchGe 3 (1), .branchGe 5 (1), .branchGe 27 (1), .branchGe 9 (1), .branchGe 6 (1)]

def plane462GenLeaf0021Mult : Fin 36 → Nat := ![4, 4, 3, 3, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 2, 2, 4, 16, 4, 4, 4, 4, 2, 2, 4, 6, 2, 4, 4, 16, 4, 12, 16]

theorem plane462GenLeaf0021 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_6 : (1 : Int) ≤ x 6)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0021Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0021Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0021Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0021Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 37
  · exact hroot.hOcc 58
  · exact hroot.hOcc 68
  · exact hroot.hOcc 71
  · exact hroot.hOcc 73
  · exact hroot.hOcc 78
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 88
  · exact hroot.hOcc 91
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 109
  · exact hroot.hOcc 165
  · exact hroot.hOcc 166
  · exact hroot.hOcc 167
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (12 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (15 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (17 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (23 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (25 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (29 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (5 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (27 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (9 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (6 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
