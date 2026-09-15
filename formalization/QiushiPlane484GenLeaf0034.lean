import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0034Refs : Fin 42 → RowRef 1665 43 := ![.occ 105, .occ 119, .occ 120, .occ 128, .occ 134, .occ 139, .occ 179, .occ 337, .occ 432, .occ 637, .occ 981, .occ 1170, .occ 1174, .occ 1208, .occ 1220, .occ 1247, .occ 1264, .occ 1274, .occ 1430, .occ 1462, .occ 1470, .occ 1500, .occ 1508, .occ 1515, .occ 1597, .occ 1602, .occ 1609, .occ 1610, .occ 1618, .sumGe, .nonneg 16, .nonneg 19, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchLe 25 (0), .branchGe 18 (1), .branchGe 1 (1)]

def plane484GenLeaf0034Mult : Fin 42 → Nat := ![766, 448, 1396, 1472, 3292, 4844, 676, 1102, 2690, 204, 947, 1687, 2131, 753, 33, 568, 308, 1000, 356, 332, 3044, 656, 445, 1612, 332, 1388, 484, 964, 168, 6568, 7496, 3108, 6568, 6568, 6568, 4708, 5180, 4952, 3806, 3108, 19000, 10308]

theorem plane484GenLeaf0034 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0034Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0034Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0034Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0034Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 128
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 179
  · exact hroot.hOcc 337
  · exact hroot.hOcc 432
  · exact hroot.hOcc 637
  · exact hroot.hOcc 981
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1247
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1274
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1500
  · exact hroot.hOcc 1508
  · exact hroot.hOcc 1515
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1618
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
