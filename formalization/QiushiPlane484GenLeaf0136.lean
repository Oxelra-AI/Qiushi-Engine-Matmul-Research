import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0136Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 128, .occ 237, .occ 275, .occ 344, .occ 368, .occ 681, .occ 724, .occ 1113, .occ 1168, .occ 1170, .occ 1172, .occ 1228, .occ 1230, .occ 1232, .occ 1238, .occ 1273, .occ 1321, .occ 1400, .occ 1421, .occ 1423, .occ 1434, .occ 1452, .occ 1504, .occ 1543, .occ 1557, .occ 1609, .occ 1620, .occ 1625, .occ 1660, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchGe 32 (1), .branchGe 37 (1), .branchLe 1 (0), .branchLe 24 (0), .branchLe 21 (0)]

def plane484GenLeaf0136Mult : Fin 43 → Nat := ![98, 1419, 1517, 18982, 10333, 14825, 630, 1877, 10235, 6113, 3271, 1763, 14087, 166, 959, 14332, 4853, 1247, 3557, 1718, 6254, 2413, 9013, 1057, 22291, 33480, 2598, 12762, 1441, 3917, 4911, 48363, 43452, 48363, 36013, 45159, 42263, 44446, 140778, 81257, 45427, 43452, 19944]

theorem plane484GenLeaf0136 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0136Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0136Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0136Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0136Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 237
  · exact hroot.hOcc 275
  · exact hroot.hOcc 344
  · exact hroot.hOcc 368
  · exact hroot.hOcc 681
  · exact hroot.hOcc 724
  · exact hroot.hOcc 1113
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1228
  · exact hroot.hOcc 1230
  · exact hroot.hOcc 1232
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1321
  · exact hroot.hOcc 1400
  · exact hroot.hOcc 1421
  · exact hroot.hOcc 1423
  · exact hroot.hOcc 1434
  · exact hroot.hOcc 1452
  · exact hroot.hOcc 1504
  · exact hroot.hOcc 1543
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1625
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
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21

end QiushiMatmul
