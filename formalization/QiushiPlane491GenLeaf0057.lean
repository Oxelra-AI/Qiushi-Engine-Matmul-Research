import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0057Refs : Fin 50 → RowRef 726 49 := ![.occ 79, .occ 89, .occ 97, .occ 100, .occ 106, .occ 113, .occ 119, .occ 153, .occ 164, .occ 166, .occ 188, .occ 219, .occ 230, .occ 232, .occ 259, .occ 284, .occ 315, .occ 338, .occ 353, .occ 360, .occ 370, .occ 389, .occ 489, .occ 511, .occ 554, .occ 569, .occ 570, .occ 590, .occ 593, .occ 603, .occ 626, .occ 634, .occ 642, .occ 644, .occ 653, .occ 660, .occ 685, .occ 692, .occ 722, .sumGe, .nonneg 8, .nonneg 13, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchLe 11 (0), .branchLe 23 (0), .branchGe 0 (1), .branchGe 39 (1), .branchGe 30 (1)]

def plane491GenLeaf0057Mult : Fin 50 → Nat := ![1871, 402, 475, 1076, 1695, 759, 1994, 163, 190, 1340, 1353, 96, 503, 1576, 1483, 767, 47, 196, 255, 786, 1332, 331, 167, 701, 268, 53, 86, 25, 111, 192, 707, 75, 982, 1028, 391, 362, 53, 1000, 333, 2776, 347, 705, 2443, 2665, 9909, 1509, 1247, 6667, 4310, 7447]

theorem plane491GenLeaf0057 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0057Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0057Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0057Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0057Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 89
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 106
  · exact hroot.hOcc 113
  · exact hroot.hOcc 119
  · exact hroot.hOcc 153
  · exact hroot.hOcc 164
  · exact hroot.hOcc 166
  · exact hroot.hOcc 188
  · exact hroot.hOcc 219
  · exact hroot.hOcc 230
  · exact hroot.hOcc 232
  · exact hroot.hOcc 259
  · exact hroot.hOcc 284
  · exact hroot.hOcc 315
  · exact hroot.hOcc 338
  · exact hroot.hOcc 353
  · exact hroot.hOcc 360
  · exact hroot.hOcc 370
  · exact hroot.hOcc 389
  · exact hroot.hOcc 489
  · exact hroot.hOcc 511
  · exact hroot.hOcc 554
  · exact hroot.hOcc 569
  · exact hroot.hOcc 570
  · exact hroot.hOcc 590
  · exact hroot.hOcc 593
  · exact hroot.hOcc 603
  · exact hroot.hOcc 626
  · exact hroot.hOcc 634
  · exact hroot.hOcc 642
  · exact hroot.hOcc 644
  · exact hroot.hOcc 653
  · exact hroot.hOcc 660
  · exact hroot.hOcc 685
  · exact hroot.hOcc 692
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (13 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (0 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (39 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (30 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30

end QiushiMatmul
