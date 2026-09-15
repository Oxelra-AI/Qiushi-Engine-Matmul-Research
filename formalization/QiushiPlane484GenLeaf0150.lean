import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0150Refs : Fin 41 → RowRef 1665 43 := ![.occ 136, .occ 140, .occ 208, .occ 307, .occ 309, .occ 334, .occ 342, .occ 352, .occ 358, .occ 371, .occ 375, .occ 376, .occ 466, .occ 475, .occ 619, .occ 620, .occ 625, .occ 658, .occ 737, .occ 1172, .occ 1215, .occ 1269, .occ 1458, .occ 1491, .occ 1551, .occ 1625, .occ 1626, .occ 1661, .sumGe, .nonneg 17, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 39 (1), .branchLe 16 (0), .branchGe 27 (1), .branchGe 24 (1), .branchLe 8 (0), .branchGe 22 (1)]

def plane484GenLeaf0150Mult : Fin 41 → Nat := ![10, 17, 2, 9, 26, 5, 7, 1, 3, 1, 6, 6, 9, 14, 3, 1, 15, 9, 2, 2, 4, 2, 5, 6, 2, 3, 8, 13, 26, 27, 9, 10, 45, 26, 26, 70, 16, 58, 61, 26, 86]

theorem plane484GenLeaf0150 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0150Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0150Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0150Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0150Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 136
  · exact hroot.hOcc 140
  · exact hroot.hOcc 208
  · exact hroot.hOcc 307
  · exact hroot.hOcc 309
  · exact hroot.hOcc 334
  · exact hroot.hOcc 342
  · exact hroot.hOcc 352
  · exact hroot.hOcc 358
  · exact hroot.hOcc 371
  · exact hroot.hOcc 375
  · exact hroot.hOcc 376
  · exact hroot.hOcc 466
  · exact hroot.hOcc 475
  · exact hroot.hOcc 619
  · exact hroot.hOcc 620
  · exact hroot.hOcc 625
  · exact hroot.hOcc 658
  · exact hroot.hOcc 737
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1551
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
