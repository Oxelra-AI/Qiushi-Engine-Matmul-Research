import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0451Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 125, .occ 126, .occ 133, .occ 148, .occ 155, .occ 191, .occ 298, .occ 325, .occ 674, .occ 702, .occ 860, .occ 997, .occ 1075, .occ 1082, .occ 1136, .occ 1140, .occ 1188, .occ 1203, .occ 1262, .occ 1267, .occ 1276, .occ 1308, .occ 1310, .occ 1515, .occ 1528, .occ 1567, .occ 1575, .occ 1592, .occ 1618, .occ 1643, .occ 1646, .occ 1656, .sumGe, .nonneg 19, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchGe 29 (1), .branchLe 27 (0), .branchLe 42 (0), .branchLe 40 (0), .branchLe 28 (0)]

def plane484GenLeaf0451Mult : Fin 44 → Nat := ![3071, 2438, 1091, 5105, 1376, 4785, 2686, 1610, 1846, 2159, 1874, 1797, 1995, 593, 4969, 2048, 1402, 1744, 3333, 1165, 4374, 3405, 394, 3649, 1384, 1516, 3172, 1903, 67, 259, 2205, 3727, 3351, 18126, 930, 23294, 13021, 16776, 15819, 34271, 16382, 18126, 18126, 14954]

theorem plane484GenLeaf0451 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0451Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0451Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0451Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0451Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 133
  · exact hroot.hOcc 148
  · exact hroot.hOcc 155
  · exact hroot.hOcc 191
  · exact hroot.hOcc 298
  · exact hroot.hOcc 325
  · exact hroot.hOcc 674
  · exact hroot.hOcc 702
  · exact hroot.hOcc 860
  · exact hroot.hOcc 997
  · exact hroot.hOcc 1075
  · exact hroot.hOcc 1082
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1203
  · exact hroot.hOcc 1262
  · exact hroot.hOcc 1267
  · exact hroot.hOcc 1276
  · exact hroot.hOcc 1308
  · exact hroot.hOcc 1310
  · exact hroot.hOcc 1515
  · exact hroot.hOcc 1528
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1575
  · exact hroot.hOcc 1592
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1643
  · exact hroot.hOcc 1646
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
