import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0371Refs : Fin 29 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 125, .occ 130, .occ 133, .occ 137, .occ 138, .occ 266, .occ 288, .occ 330, .occ 434, .occ 860, .occ 1146, .occ 1228, .occ 1322, .occ 1413, .occ 1491, .occ 1554, .sumGe, .nonneg 6, .nonneg 8, .nonneg 13, .nonneg 14, .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchLe 35 (0), .branchGe 3 (1), .branchGe 9 (1)]

def plane484GenLeaf0371Mult : Fin 29 → Nat := ![4, 6, 2, 4, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2, 2, 4, 2, 6, 6, 2, 14, 2, 12, 2, 16, 6, 26, 18]

theorem plane484GenLeaf0371 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0371Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0371Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0371Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0371Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 266
  · exact hroot.hOcc 288
  · exact hroot.hOcc 330
  · exact hroot.hOcc 434
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1228
  · exact hroot.hOcc 1322
  · exact hroot.hOcc 1413
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1554
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
