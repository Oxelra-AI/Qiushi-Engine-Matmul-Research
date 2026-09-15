import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0225Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 122, .occ 125, .occ 130, .occ 135, .occ 139, .occ 141, .occ 290, .occ 299, .occ 392, .occ 859, .occ 1136, .occ 1143, .occ 1170, .occ 1174, .occ 1188, .occ 1233, .occ 1234, .occ 1247, .occ 1319, .occ 1336, .occ 1351, .occ 1400, .occ 1459, .occ 1470, .occ 1483, .occ 1495, .occ 1580, .occ 1597, .occ 1609, .occ 1620, .occ 1648, .sumGe, .nonneg 15, .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchLe 16 (0), .branchLe 31 (0), .branchLe 22 (0), .branchGe 18 (1)]

def plane484GenLeaf0225Mult : Fin 44 → Nat := ![597, 2670, 4508, 391, 7346, 686, 2782, 1328, 138, 5664, 2260, 1610, 132, 198, 1387, 422, 954, 1005, 734, 67, 351, 86, 2043, 66, 1935, 4924, 264, 3046, 3178, 3736, 2326, 316, 12968, 40, 7204, 10668, 12902, 330, 11358, 2514, 8960, 11812, 12968, 25544]

theorem plane484GenLeaf0225 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0225Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0225Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0225Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0225Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 290
  · exact hroot.hOcc 299
  · exact hroot.hOcc 392
  · exact hroot.hOcc 859
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1247
  · exact hroot.hOcc 1319
  · exact hroot.hOcc 1336
  · exact hroot.hOcc 1351
  · exact hroot.hOcc 1400
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1495
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1648
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
