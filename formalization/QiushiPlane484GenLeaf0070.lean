import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0070Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 139, .occ 739, .occ 1019, .occ 1173, .occ 1179, .occ 1190, .occ 1213, .occ 1214, .occ 1278, .occ 1282, .occ 1346, .occ 1368, .occ 1379, .occ 1384, .occ 1397, .occ 1399, .occ 1400, .occ 1458, .occ 1459, .occ 1462, .occ 1483, .occ 1530, .occ 1531, .occ 1532, .occ 1624, .occ 1628, .occ 1635, .occ 1650, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchGe 42 (1), .branchLe 9 (0), .branchLe 20 (0), .branchLe 7 (0), .branchLe 8 (0), .branchLe 3 (0), .branchLe 27 (0), .branchLe 0 (0)]

def plane484GenLeaf0070Mult : Fin 44 → Nat := ![5092, 3732, 29026, 34464, 7843, 15548, 12172, 11582, 9522, 1663, 8747, 15317, 1614, 6379, 4181, 20173, 21673, 12427, 4040, 6056, 7877, 22051, 1553, 8767, 1896, 6847, 14499, 1271, 23246, 595, 93965, 92412, 57584, 80130, 66392, 51426, 71426, 72476, 87586, 31644, 54966, 92694, 57386, 58826]

theorem plane484GenLeaf0070 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0070Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0070Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0070Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0070Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 139
  · exact hroot.hOcc 739
  · exact hroot.hOcc 1019
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1346
  · exact hroot.hOcc 1368
  · exact hroot.hOcc 1379
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1397
  · exact hroot.hOcc 1399
  · exact hroot.hOcc 1400
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1530
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1532
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1635
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
