import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0163Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 127, .occ 504, .occ 508, .occ 510, .occ 515, .occ 778, .occ 838, .occ 848, .occ 1081, .occ 1151, .occ 1154, .occ 1164, .occ 1215, .occ 1246, .occ 1284, .occ 1315, .occ 1344, .occ 1390, .occ 1395, .occ 1403, .occ 1406, .occ 1448, .occ 1455, .occ 1491, .occ 1531, .occ 1548, .occ 1608, .occ 1647, .occ 1651, .occ 1656, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchGe 30 (1), .branchLe 20 (0), .branchLe 33 (0), .branchLe 0 (0), .branchLe 14 (0), .branchGe 41 (1)]

def plane484GenLeaf0163Mult : Fin 44 → Nat := ![3167, 1396, 8006, 1087, 2688, 3342, 1769, 483, 594, 882, 1114, 239, 2323, 284, 2219, 379, 1678, 799, 3243, 325, 633, 5, 1225, 1364, 951, 2200, 810, 294, 964, 799, 2810, 9809, 7329, 7894, 1682, 9809, 17407, 6999, 15832, 8766, 8851, 7192, 4634, 22579]

theorem plane484GenLeaf0163 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0163Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0163Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0163Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0163Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 504
  · exact hroot.hOcc 508
  · exact hroot.hOcc 510
  · exact hroot.hOcc 515
  · exact hroot.hOcc 778
  · exact hroot.hOcc 838
  · exact hroot.hOcc 848
  · exact hroot.hOcc 1081
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1246
  · exact hroot.hOcc 1284
  · exact hroot.hOcc 1315
  · exact hroot.hOcc 1344
  · exact hroot.hOcc 1390
  · exact hroot.hOcc 1395
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1406
  · exact hroot.hOcc 1448
  · exact hroot.hOcc 1455
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1548
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1651
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41

end QiushiMatmul
