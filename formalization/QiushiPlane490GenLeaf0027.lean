import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0027Refs : Fin 42 → RowRef 713 43 := ![.occ 89, .occ 91, .occ 94, .occ 98, .occ 110, .occ 117, .occ 198, .occ 203, .occ 204, .occ 217, .occ 239, .occ 272, .occ 284, .occ 302, .occ 326, .occ 332, .occ 363, .occ 366, .occ 395, .occ 499, .occ 501, .occ 533, .occ 592, .occ 599, .occ 609, .occ 667, .occ 679, .occ 680, .occ 710, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchLe 35 (0), .branchLe 5 (0), .branchLe 38 (0), .branchLe 25 (0), .branchLe 15 (0), .branchLe 24 (0), .branchLe 26 (0)]

def plane490GenLeaf0027Mult : Fin 42 → Nat := ![7, 5, 4, 5, 5, 7, 2, 11, 5, 6, 17, 8, 7, 5, 11, 9, 14, 4, 14, 2, 3, 9, 6, 13, 10, 3, 2, 5, 13, 45, 36, 34, 18, 22, 23, 45, 36, 35, 32, 45, 37, 43]

theorem plane490GenLeaf0027 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0027Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0027Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0027Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0027Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 98
  · exact hroot.hOcc 110
  · exact hroot.hOcc 117
  · exact hroot.hOcc 198
  · exact hroot.hOcc 203
  · exact hroot.hOcc 204
  · exact hroot.hOcc 217
  · exact hroot.hOcc 239
  · exact hroot.hOcc 272
  · exact hroot.hOcc 284
  · exact hroot.hOcc 302
  · exact hroot.hOcc 326
  · exact hroot.hOcc 332
  · exact hroot.hOcc 363
  · exact hroot.hOcc 366
  · exact hroot.hOcc 395
  · exact hroot.hOcc 499
  · exact hroot.hOcc 501
  · exact hroot.hOcc 533
  · exact hroot.hOcc 592
  · exact hroot.hOcc 599
  · exact hroot.hOcc 609
  · exact hroot.hOcc 667
  · exact hroot.hOcc 679
  · exact hroot.hOcc 680
  · exact hroot.hOcc 710
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
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26

end QiushiMatmul
