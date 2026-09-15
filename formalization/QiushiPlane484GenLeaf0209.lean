import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0209Refs : Fin 42 → RowRef 1665 43 := ![.occ 128, .occ 132, .occ 134, .occ 144, .occ 168, .occ 169, .occ 242, .occ 326, .occ 383, .occ 670, .occ 677, .occ 712, .occ 777, .occ 787, .occ 1101, .occ 1160, .occ 1208, .occ 1214, .occ 1270, .occ 1285, .occ 1286, .occ 1320, .occ 1351, .occ 1391, .occ 1417, .occ 1429, .occ 1471, .occ 1488, .occ 1516, .occ 1529, .occ 1541, .occ 1551, .occ 1623, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchGe 18 (1), .branchLe 38 (0), .branchLe 37 (0)]

def plane484GenLeaf0209Mult : Fin 42 → Nat := ![687, 1302, 2623, 15, 684, 1177, 2605, 548, 3774, 2480, 124, 30, 1624, 288, 30, 1336, 715, 30, 71, 472, 306, 993, 138, 1860, 15, 268, 1195, 15, 1443, 254, 185, 1951, 2657, 5295, 5280, 5280, 18307, 11591, 762, 21261, 1972, 5295]

theorem plane484GenLeaf0209 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0209Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0209Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0209Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0209Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 144
  · exact hroot.hOcc 168
  · exact hroot.hOcc 169
  · exact hroot.hOcc 242
  · exact hroot.hOcc 326
  · exact hroot.hOcc 383
  · exact hroot.hOcc 670
  · exact hroot.hOcc 677
  · exact hroot.hOcc 712
  · exact hroot.hOcc 777
  · exact hroot.hOcc 787
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1285
  · exact hroot.hOcc 1286
  · exact hroot.hOcc 1320
  · exact hroot.hOcc 1351
  · exact hroot.hOcc 1391
  · exact hroot.hOcc 1417
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1541
  · exact hroot.hOcc 1551
  · exact hroot.hOcc 1623
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37

end QiushiMatmul
