import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0517Refs : Fin 43 → RowRef 1665 43 := ![.occ 123, .occ 125, .occ 129, .occ 131, .occ 135, .occ 142, .occ 216, .occ 593, .occ 595, .occ 712, .occ 749, .occ 774, .occ 783, .occ 787, .occ 803, .occ 861, .occ 1303, .occ 1377, .occ 1391, .occ 1392, .occ 1397, .occ 1429, .occ 1430, .occ 1467, .occ 1470, .occ 1471, .occ 1483, .occ 1484, .occ 1486, .occ 1527, .occ 1595, .occ 1615, .occ 1640, .occ 1649, .sumGe, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchLe 34 (0), .branchGe 8 (1), .branchGe 42 (1)]

def plane484GenLeaf0517Mult : Fin 43 → Nat := ![542, 2806, 2216, 5367, 1670, 417, 508, 3930, 2734, 1486, 478, 1192, 410, 5850, 1178, 3218, 3646, 478, 507, 321, 1026, 702, 1932, 4070, 271, 271, 1039, 337, 1852, 2746, 495, 1026, 780, 701, 9026, 15694, 22158, 2712, 4164, 9026, 9026, 24322, 15400]

theorem plane484GenLeaf0517 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0517Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0517Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0517Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0517Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 135
  · exact hroot.hOcc 142
  · exact hroot.hOcc 216
  · exact hroot.hOcc 593
  · exact hroot.hOcc 595
  · exact hroot.hOcc 712
  · exact hroot.hOcc 749
  · exact hroot.hOcc 774
  · exact hroot.hOcc 783
  · exact hroot.hOcc 787
  · exact hroot.hOcc 803
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1377
  · exact hroot.hOcc 1391
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1397
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1527
  · exact hroot.hOcc 1595
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1640
  · exact hroot.hOcc 1649
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
