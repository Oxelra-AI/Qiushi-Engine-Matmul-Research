import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0247Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 124, .occ 125, .occ 127, .occ 130, .occ 134, .occ 136, .occ 137, .occ 139, .occ 199, .occ 354, .occ 380, .occ 399, .occ 814, .occ 856, .occ 858, .occ 1119, .occ 1142, .occ 1150, .occ 1158, .occ 1196, .occ 1220, .occ 1231, .occ 1277, .occ 1278, .occ 1282, .occ 1292, .occ 1429, .occ 1444, .occ 1470, .occ 1549, .occ 1615, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchGe 16 (1), .branchLe 13 (0), .branchLe 41 (0), .branchGe 4 (1)]

def plane484GenLeaf0247Mult : Fin 44 → Nat := ![837, 1747, 4543, 536, 1145, 670, 3474, 3158, 620, 1042, 1268, 310, 366, 922, 262, 388, 60, 2046, 1680, 490, 822, 298, 616, 86, 530, 1162, 1418, 172, 388, 1288, 768, 4070, 6840, 474, 7352, 264, 2538, 3062, 6840, 208, 13998, 3888, 6840, 15892]

theorem plane484GenLeaf0247 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0247Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0247Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0247Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0247Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 199
  · exact hroot.hOcc 354
  · exact hroot.hOcc 380
  · exact hroot.hOcc 399
  · exact hroot.hOcc 814
  · exact hroot.hOcc 856
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1119
  · exact hroot.hOcc 1142
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1231
  · exact hroot.hOcc 1277
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1292
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1444
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1549
  · exact hroot.hOcc 1615
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
