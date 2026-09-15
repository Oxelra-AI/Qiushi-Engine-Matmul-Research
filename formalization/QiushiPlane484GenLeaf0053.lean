import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0053Refs : Fin 38 → RowRef 1665 43 := ![.occ 121, .occ 136, .occ 372, .occ 708, .occ 794, .occ 974, .occ 995, .occ 1027, .occ 1030, .occ 1238, .occ 1260, .occ 1368, .occ 1374, .occ 1375, .occ 1524, .occ 1531, .occ 1532, .occ 1533, .occ 1546, .occ 1547, .occ 1549, .occ 1609, .occ 1624, .occ 1626, .occ 1655, .sumGe, .nonneg 13, .nonneg 23, .nonneg 25, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 17 (1), .branchGe 7 (1), .branchLe 10 (0), .branchLe 26 (0), .branchGe 5 (1)]

def plane484GenLeaf0053Mult : Fin 38 → Nat := ![180, 40, 48, 72, 110, 16, 32, 44, 50, 41, 31, 6, 28, 40, 6, 3, 74, 28, 26, 35, 20, 28, 86, 26, 32, 212, 424, 36, 40, 212, 172, 212, 58, 426, 578, 154, 76, 696]

theorem plane484GenLeaf0053 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0053Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0053Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0053Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0053Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 136
  · exact hroot.hOcc 372
  · exact hroot.hOcc 708
  · exact hroot.hOcc 794
  · exact hroot.hOcc 974
  · exact hroot.hOcc 995
  · exact hroot.hOcc 1027
  · exact hroot.hOcc 1030
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1368
  · exact hroot.hOcc 1374
  · exact hroot.hOcc 1375
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1532
  · exact hroot.hOcc 1533
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1549
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
