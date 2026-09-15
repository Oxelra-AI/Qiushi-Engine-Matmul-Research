import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0382Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 131, .occ 133, .occ 136, .occ 138, .occ 180, .occ 709, .occ 712, .occ 754, .occ 774, .occ 787, .occ 800, .occ 1147, .occ 1186, .occ 1206, .occ 1213, .occ 1251, .occ 1397, .occ 1434, .occ 1456, .occ 1481, .occ 1483, .occ 1488, .occ 1495, .occ 1496, .occ 1571, .occ 1597, .occ 1602, .occ 1606, .occ 1633, .occ 1658, .occ 1664, .sumGe, .nonneg 15, .nonneg 20, .nonneg 25, .nonneg 26, .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchLe 30 (0), .branchGe 42 (1), .branchGe 19 (1)]

def plane484GenLeaf0382Mult : Fin 44 → Nat := ![14232, 95862, 93720, 9722, 21965, 49889, 18188, 53310, 5776, 12466, 758, 9772, 16631, 1529, 3106, 13402, 2230, 6408, 1580, 4362, 3064, 56342, 10100, 31264, 60339, 45091, 5792, 11952, 9006, 42517, 4804, 4004, 120824, 201496, 7036, 824, 20628, 241861, 24408, 277740, 186320, 120824, 220384, 271674]

theorem plane484GenLeaf0382 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0382Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0382Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0382Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0382Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 180
  · exact hroot.hOcc 709
  · exact hroot.hOcc 712
  · exact hroot.hOcc 754
  · exact hroot.hOcc 774
  · exact hroot.hOcc 787
  · exact hroot.hOcc 800
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1251
  · exact hroot.hOcc 1397
  · exact hroot.hOcc 1434
  · exact hroot.hOcc 1456
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1495
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1633
  · exact hroot.hOcc 1658
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19

end QiushiMatmul
