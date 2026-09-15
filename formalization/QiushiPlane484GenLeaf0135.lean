import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0135Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 128, .occ 134, .occ 149, .occ 344, .occ 382, .occ 434, .occ 494, .occ 552, .occ 582, .occ 955, .occ 1095, .occ 1151, .occ 1164, .occ 1215, .occ 1222, .occ 1226, .occ 1230, .occ 1273, .occ 1358, .occ 1381, .occ 1423, .occ 1429, .occ 1501, .occ 1529, .occ 1557, .occ 1558, .occ 1609, .occ 1623, .occ 1652, .occ 1660, .occ 1663, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchGe 32 (1), .branchLe 37 (0), .branchGe 3 (1), .branchGe 38 (1)]

def plane484GenLeaf0135Mult : Fin 44 → Nat := ![3750, 3849, 4105, 2404, 12812, 2610, 7036, 1437, 5779, 7893, 2043, 537, 1576, 5752, 724, 1275, 7, 5536, 1554, 3915, 4973, 1172, 6125, 3165, 2189, 621, 544, 2969, 1102, 1015, 501, 3412, 2910, 17886, 9000, 17886, 38901, 10789, 1102, 11410, 48118, 16784, 44999, 44617]

theorem plane484GenLeaf0135 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0135Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0135Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0135Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0135Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 128
  · exact hroot.hOcc 134
  · exact hroot.hOcc 149
  · exact hroot.hOcc 344
  · exact hroot.hOcc 382
  · exact hroot.hOcc 434
  · exact hroot.hOcc 494
  · exact hroot.hOcc 552
  · exact hroot.hOcc 582
  · exact hroot.hOcc 955
  · exact hroot.hOcc 1095
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1226
  · exact hroot.hOcc 1230
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1381
  · exact hroot.hOcc 1423
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1501
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1558
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1652
  · exact hroot.hOcc 1660
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
