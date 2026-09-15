import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0043Refs : Fin 43 → RowRef 1665 43 := ![.occ 131, .occ 132, .occ 137, .occ 142, .occ 189, .occ 399, .occ 490, .occ 1136, .occ 1158, .occ 1168, .occ 1170, .occ 1190, .occ 1267, .occ 1308, .occ 1338, .occ 1358, .occ 1368, .occ 1382, .occ 1395, .occ 1428, .occ 1433, .occ 1512, .occ 1553, .occ 1567, .occ 1615, .occ 1634, .occ 1638, .occ 1639, .occ 1644, .occ 1647, .sumGe, .nonneg 2, .branchLe 15 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchGe 17 (1), .branchLe 7 (0), .branchLe 18 (0), .branchLe 1 (0), .branchLe 5 (0), .branchGe 16 (1), .branchLe 10 (0)]

def plane484GenLeaf0043Mult : Fin 43 → Nat := ![20250, 17390, 40848, 20250, 2638, 5088, 15326, 4000, 31524, 4220, 4220, 20850, 7046, 10314, 7794, 7784, 3684, 11652, 23568, 5628, 16080, 442, 2856, 44086, 16666, 23453, 25573, 16569, 37850, 1673, 126304, 84598, 29830, 78218, 55712, 67604, 165880, 100736, 104914, 126304, 30256, 233296, 94102]

theorem plane484GenLeaf0043 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0043Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0043Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0043Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0043Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 142
  · exact hroot.hOcc 189
  · exact hroot.hOcc 399
  · exact hroot.hOcc 490
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1267
  · exact hroot.hOcc 1308
  · exact hroot.hOcc 1338
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1368
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1395
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1512
  · exact hroot.hOcc 1553
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1634
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1647
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
