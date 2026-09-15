import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0314Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 123, .occ 139, .occ 141, .occ 180, .occ 386, .occ 718, .occ 808, .occ 1136, .occ 1143, .occ 1145, .occ 1146, .occ 1173, .occ 1214, .occ 1220, .occ 1353, .occ 1392, .occ 1462, .occ 1482, .occ 1492, .occ 1496, .occ 1517, .occ 1541, .occ 1557, .occ 1573, .occ 1607, .occ 1609, .occ 1636, .occ 1639, .sumGe, .nonneg 25, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchGe 26 (1), .branchLe 14 (0), .branchLe 1 (0), .branchLe 22 (0), .branchLe 16 (0), .branchGe 0 (1), .branchLe 31 (0), .branchLe 10 (0)]

def plane484GenLeaf0314Mult : Fin 43 → Nat := ![485, 10520, 5098, 11685, 675, 169, 7610, 882, 499, 2132, 4483, 4674, 2590, 4763, 1029, 5970, 652, 385, 552, 3349, 2962, 944, 578, 1168, 1616, 2671, 530, 617, 5766, 20210, 4110, 20210, 17305, 16922, 3854, 32582, 10794, 9964, 11650, 8560, 5249, 15632, 19108]

theorem plane484GenLeaf0314 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0314Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0314Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0314Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0314Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 180
  · exact hroot.hOcc 386
  · exact hroot.hOcc 718
  · exact hroot.hOcc 808
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1482
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1541
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1636
  · exact hroot.hOcc 1639
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
