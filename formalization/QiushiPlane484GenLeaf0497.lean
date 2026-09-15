import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0497Refs : Fin 39 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 124, .occ 126, .occ 135, .occ 138, .occ 142, .occ 279, .occ 377, .occ 442, .occ 445, .occ 503, .occ 513, .occ 516, .occ 596, .occ 634, .occ 783, .occ 968, .occ 1015, .occ 1099, .occ 1136, .occ 1166, .occ 1329, .occ 1467, .occ 1549, .occ 1590, .occ 1622, .occ 1658, .occ 1664, .sumGe, .nonneg 0, .nonneg 2, .branchGe 15 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 32 (0), .branchLe 14 (0), .branchGe 36 (1), .branchLe 28 (0)]

def plane484GenLeaf0497Mult : Fin 39 → Nat := ![16, 39, 42, 9, 37, 47, 47, 16, 84, 24, 42, 21, 22, 33, 8, 37, 70, 3, 2, 2, 2, 21, 2, 11, 21, 47, 13, 13, 29, 110, 18, 25, 327, 110, 343, 97, 88, 283, 110]

theorem plane484GenLeaf0497 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0497Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0497Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0497Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0497Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 279
  · exact hroot.hOcc 377
  · exact hroot.hOcc 442
  · exact hroot.hOcc 445
  · exact hroot.hOcc 503
  · exact hroot.hOcc 513
  · exact hroot.hOcc 516
  · exact hroot.hOcc 596
  · exact hroot.hOcc 634
  · exact hroot.hOcc 783
  · exact hroot.hOcc 968
  · exact hroot.hOcc 1015
  · exact hroot.hOcc 1099
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1329
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1549
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1658
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
