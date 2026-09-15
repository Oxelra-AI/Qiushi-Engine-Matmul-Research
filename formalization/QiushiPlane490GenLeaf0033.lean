import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0033Refs : Fin 44 → RowRef 713 43 := ![.occ 91, .occ 94, .occ 96, .occ 100, .occ 109, .occ 113, .occ 146, .occ 205, .occ 247, .occ 270, .occ 272, .occ 290, .occ 302, .occ 303, .occ 322, .occ 336, .occ 346, .occ 362, .occ 366, .occ 379, .occ 435, .occ 449, .occ 454, .occ 501, .occ 532, .occ 599, .occ 602, .occ 607, .occ 664, .occ 665, .occ 676, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchLe 35 (0), .branchLe 5 (0), .branchLe 38 (0), .branchLe 25 (0), .branchGe 15 (1), .branchLe 3 (0), .branchGe 14 (1)]

def plane490GenLeaf0033Mult : Fin 44 → Nat := ![371, 21, 61, 638, 475, 597, 24, 923, 229, 526, 39, 260, 90, 636, 238, 270, 289, 318, 817, 379, 105, 474, 317, 56, 138, 320, 146, 208, 327, 54, 702, 1543, 1133, 1137, 926, 898, 1225, 1489, 620, 1453, 817, 1845, 642, 3932]

theorem plane490GenLeaf0033 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0033Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0033Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0033Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0033Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 96
  · exact hroot.hOcc 100
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 146
  · exact hroot.hOcc 205
  · exact hroot.hOcc 247
  · exact hroot.hOcc 270
  · exact hroot.hOcc 272
  · exact hroot.hOcc 290
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 322
  · exact hroot.hOcc 336
  · exact hroot.hOcc 346
  · exact hroot.hOcc 362
  · exact hroot.hOcc 366
  · exact hroot.hOcc 379
  · exact hroot.hOcc 435
  · exact hroot.hOcc 449
  · exact hroot.hOcc 454
  · exact hroot.hOcc 501
  · exact hroot.hOcc 532
  · exact hroot.hOcc 599
  · exact hroot.hOcc 602
  · exact hroot.hOcc 607
  · exact hroot.hOcc 664
  · exact hroot.hOcc 665
  · exact hroot.hOcc 676
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
