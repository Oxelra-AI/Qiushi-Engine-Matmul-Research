import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0420Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 124, .occ 126, .occ 127, .occ 131, .occ 134, .occ 137, .occ 154, .occ 307, .occ 505, .occ 688, .occ 707, .occ 824, .occ 858, .occ 1132, .occ 1154, .occ 1164, .occ 1196, .occ 1235, .occ 1352, .occ 1357, .occ 1380, .occ 1481, .occ 1484, .occ 1486, .occ 1496, .occ 1511, .occ 1558, .occ 1567, .occ 1601, .occ 1606, .occ 1607, .sumGe, .nonneg 17, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchGe 31 (1), .branchGe 29 (1), .branchLe 36 (0), .branchLe 34 (0), .branchLe 8 (0), .branchGe 20 (1)]

def plane484GenLeaf0420Mult : Fin 44 → Nat := ![1093, 243, 596, 1598, 62, 416, 854, 533, 371, 2952, 226, 908, 2072, 1999, 475, 1548, 221, 709, 389, 997, 208, 535, 356, 239, 1598, 239, 344, 325, 520, 148, 208, 239, 3562, 398, 398, 3791, 7488, 1024, 6903, 6566, 2122, 2879, 2009, 11397]

theorem plane484GenLeaf0420 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0420Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0420Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0420Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0420Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 131
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 154
  · exact hroot.hOcc 307
  · exact hroot.hOcc 505
  · exact hroot.hOcc 688
  · exact hroot.hOcc 707
  · exact hroot.hOcc 824
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1132
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1235
  · exact hroot.hOcc 1352
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1380
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1511
  · exact hroot.hOcc 1558
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1607
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
