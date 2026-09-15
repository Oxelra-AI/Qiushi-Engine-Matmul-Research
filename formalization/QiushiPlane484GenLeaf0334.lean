import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0334Refs : Fin 44 → RowRef 1665 43 := ![.occ 86, .occ 128, .occ 130, .occ 139, .occ 289, .occ 391, .occ 452, .occ 581, .occ 584, .occ 827, .occ 1001, .occ 1064, .occ 1146, .occ 1183, .occ 1205, .occ 1321, .occ 1357, .occ 1459, .occ 1486, .occ 1489, .occ 1573, .occ 1580, .occ 1593, .occ 1604, .occ 1607, .occ 1620, .occ 1641, .occ 1655, .occ 1659, .sumGe, .nonneg 6, .nonneg 19, .branchLe 15 (0), .branchLe 7 (0), .branchLe 23 (0), .branchGe 26 (1), .branchLe 14 (0), .branchGe 1 (1), .branchGe 30 (1), .branchLe 36 (0), .branchGe 27 (1), .branchLe 17 (0), .branchLe 38 (0), .branchGe 10 (1)]

def plane484GenLeaf0334Mult : Fin 44 → Nat := ![151, 396, 263, 708, 157, 408, 1292, 124, 727, 30, 333, 771, 138, 107, 165, 18, 214, 30, 584, 126, 48, 18, 247, 164, 144, 263, 107, 340, 370, 1418, 108, 137, 652, 319, 648, 4385, 138, 610, 890, 1245, 3201, 515, 1173, 5082]

theorem plane484GenLeaf0334 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0334Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0334Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0334Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0334Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 139
  · exact hroot.hOcc 289
  · exact hroot.hOcc 391
  · exact hroot.hOcc 452
  · exact hroot.hOcc 581
  · exact hroot.hOcc 584
  · exact hroot.hOcc 827
  · exact hroot.hOcc 1001
  · exact hroot.hOcc 1064
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1321
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1593
  · exact hroot.hOcc 1604
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1641
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
