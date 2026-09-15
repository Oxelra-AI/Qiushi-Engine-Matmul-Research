import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0121Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 132, .occ 139, .occ 141, .occ 247, .occ 271, .occ 462, .occ 1062, .occ 1070, .occ 1154, .occ 1160, .occ 1161, .occ 1230, .occ 1271, .occ 1315, .occ 1337, .occ 1390, .occ 1406, .occ 1407, .occ 1427, .occ 1477, .occ 1491, .occ 1501, .occ 1505, .occ 1507, .occ 1558, .occ 1619, .occ 1622, .occ 1650, .occ 1664, .sumGe, .nonneg 10, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchLe 32 (0), .branchLe 28 (0), .branchLe 5 (0), .branchGe 6 (1)]

def plane484GenLeaf0121Mult : Fin 43 → Nat := ![3108, 6280, 428, 1930, 2484, 1360, 934, 1108, 1302, 2881, 864, 1427, 483, 1117, 2852, 1847, 1374, 680, 33, 2922, 2027, 2635, 2732, 1486, 959, 733, 483, 532, 2567, 155, 835, 11864, 814, 5078, 9132, 18766, 9323, 1922, 9757, 11864, 10378, 5325, 23129]

theorem plane484GenLeaf0121 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0121Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0121Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0121Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0121Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 132
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 247
  · exact hroot.hOcc 271
  · exact hroot.hOcc 462
  · exact hroot.hOcc 1062
  · exact hroot.hOcc 1070
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1161
  · exact hroot.hOcc 1230
  · exact hroot.hOcc 1271
  · exact hroot.hOcc 1315
  · exact hroot.hOcc 1337
  · exact hroot.hOcc 1390
  · exact hroot.hOcc 1406
  · exact hroot.hOcc 1407
  · exact hroot.hOcc 1427
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1501
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1507
  · exact hroot.hOcc 1558
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1650
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
