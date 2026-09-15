import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0049Refs : Fin 42 → RowRef 1665 43 := ![.occ 133, .occ 139, .occ 140, .occ 142, .occ 381, .occ 648, .occ 673, .occ 755, .occ 821, .occ 830, .occ 834, .occ 1069, .occ 1124, .occ 1158, .occ 1205, .occ 1206, .occ 1213, .occ 1220, .occ 1231, .occ 1267, .occ 1278, .occ 1342, .occ 1347, .occ 1357, .occ 1368, .occ 1470, .occ 1472, .occ 1590, .occ 1610, .occ 1663, .sumGe, .nonneg 15, .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchGe 17 (1), .branchLe 7 (0), .branchLe 18 (0), .branchGe 1 (1), .branchGe 38 (1), .branchGe 35 (1)]

def plane484GenLeaf0049Mult : Fin 42 → Nat := ![18481, 3030, 24033, 3268, 17599, 3034, 9076, 7327, 6274, 13574, 12668, 12425, 4129, 9340, 14770, 46, 7244, 6085, 2582, 1440, 295, 2565, 213, 1675, 1539, 8668, 2834, 1615, 9810, 1692, 31870, 39683, 31870, 30255, 30178, 31870, 121624, 28563, 8670, 52980, 59665, 66984]

theorem plane484GenLeaf0049 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0049Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0049Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0049Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0049Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 133
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 381
  · exact hroot.hOcc 648
  · exact hroot.hOcc 673
  · exact hroot.hOcc 755
  · exact hroot.hOcc 821
  · exact hroot.hOcc 830
  · exact hroot.hOcc 834
  · exact hroot.hOcc 1069
  · exact hroot.hOcc 1124
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1231
  · exact hroot.hOcc 1267
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1347
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1368
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
