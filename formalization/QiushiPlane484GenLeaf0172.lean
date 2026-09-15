import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0172Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 127, .occ 134, .occ 137, .occ 146, .occ 154, .occ 158, .occ 190, .occ 313, .occ 322, .occ 328, .occ 329, .occ 403, .occ 505, .occ 680, .occ 685, .occ 688, .occ 723, .occ 824, .occ 828, .occ 1018, .occ 1150, .occ 1273, .occ 1288, .occ 1302, .occ 1467, .occ 1489, .occ 1511, .occ 1550, .occ 1601, .occ 1608, .occ 1653, .occ 1664, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchGe 30 (1), .branchGe 20 (1), .branchLe 5 (0), .branchGe 31 (1)]

def plane484GenLeaf0172Mult : Fin 44 → Nat := ![440, 19, 728, 194, 587, 1022, 680, 63, 174, 842, 309, 98, 303, 1034, 59, 737, 198, 300, 557, 372, 395, 180, 433, 290, 98, 12, 128, 10, 101, 575, 110, 95, 7, 1132, 624, 810, 2637, 1132, 2214, 309, 3891, 4654, 1132, 7246]

theorem plane484GenLeaf0172 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0172Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0172Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0172Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0172Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 127
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 146
  · exact hroot.hOcc 154
  · exact hroot.hOcc 158
  · exact hroot.hOcc 190
  · exact hroot.hOcc 313
  · exact hroot.hOcc 322
  · exact hroot.hOcc 328
  · exact hroot.hOcc 329
  · exact hroot.hOcc 403
  · exact hroot.hOcc 505
  · exact hroot.hOcc 680
  · exact hroot.hOcc 685
  · exact hroot.hOcc 688
  · exact hroot.hOcc 723
  · exact hroot.hOcc 824
  · exact hroot.hOcc 828
  · exact hroot.hOcc 1018
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1288
  · exact hroot.hOcc 1302
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1511
  · exact hroot.hOcc 1550
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1653
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31

end QiushiMatmul
