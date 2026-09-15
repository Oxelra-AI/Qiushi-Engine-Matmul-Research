import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0000Refs : Fin 44 → RowRef 1665 43 := ![.occ 131, .occ 141, .occ 142, .occ 207, .occ 260, .occ 290, .occ 562, .occ 615, .occ 720, .occ 1146, .occ 1154, .occ 1196, .occ 1226, .occ 1257, .occ 1270, .occ 1272, .occ 1275, .occ 1347, .occ 1350, .occ 1369, .occ 1371, .occ 1448, .occ 1472, .occ 1504, .occ 1510, .occ 1603, .occ 1608, .occ 1626, .occ 1628, .occ 1647, .occ 1664, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchLe 41 (0), .branchLe 8 (0), .branchLe 10 (0), .branchLe 1 (0), .branchLe 14 (0)]

def plane484GenLeaf0000Mult : Fin 44 → Nat := ![11325, 384495, 129973, 84100, 37262, 14280, 12656, 64363, 208430, 345468, 47490, 54118, 57152, 188946, 92328, 35466, 247372, 4464, 110786, 5054, 14804, 303272, 196388, 128300, 10090, 86398, 88788, 402484, 278972, 172536, 173890, 1355996, 667846, 783874, 1222108, 878834, 830926, 322028, 1155144, 1355996, 1093318, 712578, 833146, 1137904]

theorem plane484GenLeaf0000 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0000Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0000Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 131
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 207
  · exact hroot.hOcc 260
  · exact hroot.hOcc 290
  · exact hroot.hOcc 562
  · exact hroot.hOcc 615
  · exact hroot.hOcc 720
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1226
  · exact hroot.hOcc 1257
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1272
  · exact hroot.hOcc 1275
  · exact hroot.hOcc 1347
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1369
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1448
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1504
  · exact hroot.hOcc 1510
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
