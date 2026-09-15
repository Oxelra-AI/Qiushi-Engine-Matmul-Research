import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0173Refs : Fin 34 → RowRef 1665 43 := ![.occ 121, .occ 124, .occ 129, .occ 135, .occ 180, .occ 344, .occ 376, .occ 422, .occ 598, .occ 707, .occ 723, .occ 848, .occ 905, .occ 906, .occ 1022, .occ 1074, .occ 1154, .occ 1183, .occ 1239, .occ 1380, .occ 1575, .occ 1636, .occ 1660, .sumGe, .nonneg 0, .nonneg 2, .nonneg 13, .branchLe 15 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchGe 30 (1), .branchGe 20 (1), .branchGe 5 (1)]

def plane484GenLeaf0173Mult : Fin 34 → Nat := ![1, 2, 5, 2, 1, 5, 3, 1, 5, 4, 1, 1, 3, 3, 1, 1, 6, 1, 1, 2, 1, 2, 2, 7, 4, 2, 8, 1, 22, 7, 15, 4, 34, 33]

theorem plane484GenLeaf0173 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0173Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0173Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0173Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0173Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 135
  · exact hroot.hOcc 180
  · exact hroot.hOcc 344
  · exact hroot.hOcc 376
  · exact hroot.hOcc 422
  · exact hroot.hOcc 598
  · exact hroot.hOcc 707
  · exact hroot.hOcc 723
  · exact hroot.hOcc 848
  · exact hroot.hOcc 905
  · exact hroot.hOcc 906
  · exact hroot.hOcc 1022
  · exact hroot.hOcc 1074
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1239
  · exact hroot.hOcc 1380
  · exact hroot.hOcc 1575
  · exact hroot.hOcc 1636
  · exact hroot.hOcc 1660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
