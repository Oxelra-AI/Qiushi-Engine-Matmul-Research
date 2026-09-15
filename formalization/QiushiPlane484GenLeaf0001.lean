import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0001Refs : Fin 43 → RowRef 1665 43 := ![.occ 121, .occ 127, .occ 133, .occ 141, .occ 143, .occ 234, .occ 283, .occ 330, .occ 366, .occ 466, .occ 615, .occ 860, .occ 1032, .occ 1231, .occ 1270, .occ 1272, .occ 1325, .occ 1351, .occ 1371, .occ 1384, .occ 1462, .occ 1552, .occ 1554, .occ 1580, .occ 1602, .occ 1603, .occ 1626, .occ 1628, .occ 1631, .occ 1647, .occ 1664, .sumGe, .nonneg 1, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchLe 41 (0), .branchLe 8 (0), .branchGe 14 (1)]

def plane484GenLeaf0001Mult : Fin 43 → Nat := ![5950, 24708, 4786, 25701, 18952, 24, 14520, 8067, 13209, 14224, 4145, 3898, 12678, 29840, 1618, 29956, 5146, 10852, 18420, 12998, 23824, 15708, 2552, 18396, 33136, 1960, 17092, 10162, 2810, 5626, 980, 104290, 4764, 56018, 79712, 102330, 75792, 55042, 28422, 104290, 101480, 75792, 148130]

theorem plane484GenLeaf0001 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0001Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0001Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 133
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 234
  · exact hroot.hOcc 283
  · exact hroot.hOcc 330
  · exact hroot.hOcc 366
  · exact hroot.hOcc 466
  · exact hroot.hOcc 615
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1032
  · exact hroot.hOcc 1231
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1272
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1351
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1552
  · exact hroot.hOcc 1554
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
