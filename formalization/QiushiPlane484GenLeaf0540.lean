import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0540Refs : Fin 28 → RowRef 1665 43 := ![.occ 122, .occ 133, .occ 138, .occ 171, .occ 196, .occ 246, .occ 295, .occ 330, .occ 363, .occ 377, .occ 427, .occ 800, .occ 859, .occ 866, .occ 1008, .occ 1158, .occ 1274, .occ 1401, .occ 1506, .sumGe, .nonneg 23, .nonneg 25, .branchGe 15 (1), .branchGe 35 (1), .branchLe 26 (0), .branchGe 30 (1), .branchGe 19 (1), .branchGe 6 (1)]

def plane484GenLeaf0540Mult : Fin 28 → Nat := ![1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 8, 4, 1, 10, 6, 11]

theorem plane484GenLeaf0540 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0540Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0540Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0540Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0540Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 171
  · exact hroot.hOcc 196
  · exact hroot.hOcc 246
  · exact hroot.hOcc 295
  · exact hroot.hOcc 330
  · exact hroot.hOcc 363
  · exact hroot.hOcc 377
  · exact hroot.hOcc 427
  · exact hroot.hOcc 800
  · exact hroot.hOcc 859
  · exact hroot.hOcc 866
  · exact hroot.hOcc 1008
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1274
  · exact hroot.hOcc 1401
  · exact hroot.hOcc 1506
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
