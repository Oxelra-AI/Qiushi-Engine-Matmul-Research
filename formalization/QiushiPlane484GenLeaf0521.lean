import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0521Refs : Fin 42 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 126, .occ 138, .occ 199, .occ 278, .occ 288, .occ 296, .occ 381, .occ 390, .occ 581, .occ 596, .occ 647, .occ 674, .occ 700, .occ 857, .occ 953, .occ 1050, .occ 1124, .occ 1154, .occ 1159, .occ 1179, .occ 1314, .occ 1358, .occ 1418, .occ 1424, .occ 1496, .occ 1571, .occ 1597, .occ 1615, .occ 1652, .occ 1664, .sumGe, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchGe 34 (1), .branchLe 9 (0), .branchLe 18 (0), .branchGe 3 (1)]

def plane484GenLeaf0521Mult : Fin 42 → Nat := ![395, 207, 711, 509, 384, 72, 72, 465, 1018, 254, 176, 125, 722, 196, 373, 273, 691, 130, 83, 72, 530, 250, 254, 474, 578, 275, 21, 125, 472, 227, 125, 342, 1573, 3916, 3655, 1198, 176, 1501, 4589, 393, 1064, 5796]

theorem plane484GenLeaf0521 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0521Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0521Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0521Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0521Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 138
  · exact hroot.hOcc 199
  · exact hroot.hOcc 278
  · exact hroot.hOcc 288
  · exact hroot.hOcc 296
  · exact hroot.hOcc 381
  · exact hroot.hOcc 390
  · exact hroot.hOcc 581
  · exact hroot.hOcc 596
  · exact hroot.hOcc 647
  · exact hroot.hOcc 674
  · exact hroot.hOcc 700
  · exact hroot.hOcc 857
  · exact hroot.hOcc 953
  · exact hroot.hOcc 1050
  · exact hroot.hOcc 1124
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1314
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1418
  · exact hroot.hOcc 1424
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1652
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
