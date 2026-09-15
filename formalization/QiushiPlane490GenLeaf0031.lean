import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0031Refs : Fin 43 → RowRef 713 43 := ![.occ 91, .occ 109, .occ 174, .occ 188, .occ 247, .occ 283, .occ 284, .occ 292, .occ 295, .occ 302, .occ 305, .occ 314, .occ 324, .occ 326, .occ 332, .occ 356, .occ 379, .occ 395, .occ 480, .occ 501, .occ 503, .occ 506, .occ 510, .occ 533, .occ 542, .occ 575, .occ 668, .occ 680, .occ 694, .occ 710, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchLe 35 (0), .branchLe 38 (0), .branchGe 15 (1), .branchLe 3 (0), .branchLe 14 (0), .branchLe 24 (0), .branchGe 42 (1)]

def plane490GenLeaf0031Mult : Fin 43 → Nat := ![536, 183, 13, 230, 170, 31, 624, 233, 209, 407, 476, 504, 19, 50, 186, 110, 473, 498, 646, 173, 236, 303, 29, 208, 766, 303, 794, 73, 63, 63, 1573, 1371, 598, 2567, 7, 854, 1544, 416, 2193, 999, 861, 1034, 4356]

theorem plane490GenLeaf0031 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0031Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0031Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0031Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0031Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 109
  · exact hroot.hOcc 174
  · exact hroot.hOcc 188
  · exact hroot.hOcc 247
  · exact hroot.hOcc 283
  · exact hroot.hOcc 284
  · exact hroot.hOcc 292
  · exact hroot.hOcc 295
  · exact hroot.hOcc 302
  · exact hroot.hOcc 305
  · exact hroot.hOcc 314
  · exact hroot.hOcc 324
  · exact hroot.hOcc 326
  · exact hroot.hOcc 332
  · exact hroot.hOcc 356
  · exact hroot.hOcc 379
  · exact hroot.hOcc 395
  · exact hroot.hOcc 480
  · exact hroot.hOcc 501
  · exact hroot.hOcc 503
  · exact hroot.hOcc 506
  · exact hroot.hOcc 510
  · exact hroot.hOcc 533
  · exact hroot.hOcc 542
  · exact hroot.hOcc 575
  · exact hroot.hOcc 668
  · exact hroot.hOcc 680
  · exact hroot.hOcc 694
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
