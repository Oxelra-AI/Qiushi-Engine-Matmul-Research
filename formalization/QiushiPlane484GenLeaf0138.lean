import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0138Refs : Fin 43 → RowRef 1665 43 := ![.occ 130, .occ 131, .occ 132, .occ 141, .occ 148, .occ 149, .occ 258, .occ 275, .occ 368, .occ 402, .occ 476, .occ 625, .occ 701, .occ 724, .occ 955, .occ 1129, .occ 1145, .occ 1228, .occ 1255, .occ 1261, .occ 1322, .occ 1339, .occ 1433, .occ 1434, .occ 1451, .occ 1462, .occ 1491, .occ 1502, .occ 1543, .occ 1603, .occ 1645, .occ 1660, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchGe 32 (1), .branchGe 37 (1), .branchLe 1 (0), .branchGe 24 (1)]

def plane484GenLeaf0138Mult : Fin 43 → Nat := ![666, 243, 230, 1525, 474, 104, 4, 597, 1219, 985, 844, 158, 1229, 704, 263, 688, 473, 1073, 1263, 1757, 1174, 276, 3, 383, 85, 1667, 510, 1174, 1405, 439, 190, 575, 4366, 3082, 3193, 4525, 4366, 4366, 4366, 13352, 6994, 2699, 5829]

theorem plane484GenLeaf0138 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0138Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0138Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0138Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0138Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 141
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 258
  · exact hroot.hOcc 275
  · exact hroot.hOcc 368
  · exact hroot.hOcc 402
  · exact hroot.hOcc 476
  · exact hroot.hOcc 625
  · exact hroot.hOcc 701
  · exact hroot.hOcc 724
  · exact hroot.hOcc 955
  · exact hroot.hOcc 1129
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1228
  · exact hroot.hOcc 1255
  · exact hroot.hOcc 1261
  · exact hroot.hOcc 1322
  · exact hroot.hOcc 1339
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1434
  · exact hroot.hOcc 1451
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1502
  · exact hroot.hOcc 1543
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1645
  · exact hroot.hOcc 1660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
