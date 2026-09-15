import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0104Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 130, .occ 140, .occ 247, .occ 282, .occ 288, .occ 385, .occ 649, .occ 725, .occ 728, .occ 747, .occ 837, .occ 855, .occ 1081, .occ 1143, .occ 1145, .occ 1150, .occ 1240, .occ 1256, .occ 1398, .occ 1448, .occ 1459, .occ 1473, .occ 1517, .occ 1524, .occ 1545, .occ 1580, .occ 1600, .occ 1608, .occ 1615, .occ 1630, .occ 1635, .occ 1639, .occ 1650, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchGe 26 (1), .branchGe 37 (1), .branchGe 34 (1), .branchGe 30 (1)]

def plane484GenLeaf0104Mult : Fin 44 → Nat := ![23, 31, 12, 69, 33, 20, 31, 8, 31, 1, 1, 5, 88, 45, 10, 12, 19, 11, 9, 2, 7, 4, 5, 21, 1, 31, 17, 8, 19, 11, 2, 1, 40, 2, 92, 17, 29, 92, 289, 75, 307, 226, 90, 275]

theorem plane484GenLeaf0104 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0104Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0104Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0104Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0104Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 130
  · exact hroot.hOcc 140
  · exact hroot.hOcc 247
  · exact hroot.hOcc 282
  · exact hroot.hOcc 288
  · exact hroot.hOcc 385
  · exact hroot.hOcc 649
  · exact hroot.hOcc 725
  · exact hroot.hOcc 728
  · exact hroot.hOcc 747
  · exact hroot.hOcc 837
  · exact hroot.hOcc 855
  · exact hroot.hOcc 1081
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1240
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1448
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1473
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1545
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1600
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1635
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30

end QiushiMatmul
