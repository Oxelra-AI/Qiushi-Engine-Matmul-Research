import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0169Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 134, .occ 141, .occ 386, .occ 492, .occ 504, .occ 542, .occ 682, .occ 688, .occ 723, .occ 997, .occ 1118, .occ 1173, .occ 1196, .occ 1257, .occ 1273, .occ 1380, .occ 1405, .occ 1421, .occ 1443, .occ 1486, .occ 1488, .occ 1524, .occ 1530, .occ 1563, .occ 1571, .occ 1636, .occ 1653, .sumGe, .nonneg 2, .nonneg 3, .branchLe 15 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchGe 30 (1), .branchGe 20 (1), .branchLe 5 (0), .branchLe 31 (0), .branchLe 6 (0), .branchLe 24 (0)]

def plane484GenLeaf0169Mult : Fin 43 → Nat := ![828, 542, 463, 390, 92, 385, 259, 92, 138, 273, 432, 112, 62, 152, 648, 159, 369, 169, 140, 74, 55, 176, 252, 178, 164, 50, 226, 72, 303, 1370, 96, 186, 1320, 1255, 564, 2878, 50, 993, 2982, 24, 1370, 558, 1370]

theorem plane484GenLeaf0169 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0169Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0169Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0169Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0169Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 134
  · exact hroot.hOcc 141
  · exact hroot.hOcc 386
  · exact hroot.hOcc 492
  · exact hroot.hOcc 504
  · exact hroot.hOcc 542
  · exact hroot.hOcc 682
  · exact hroot.hOcc 688
  · exact hroot.hOcc 723
  · exact hroot.hOcc 997
  · exact hroot.hOcc 1118
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1257
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1380
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1421
  · exact hroot.hOcc 1443
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1530
  · exact hroot.hOcc 1563
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1636
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24

end QiushiMatmul
