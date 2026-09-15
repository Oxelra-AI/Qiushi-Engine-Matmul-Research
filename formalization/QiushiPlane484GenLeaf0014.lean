import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0014Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 126, .occ 134, .occ 142, .occ 175, .occ 180, .occ 283, .occ 537, .occ 542, .occ 613, .occ 747, .occ 1172, .occ 1244, .occ 1351, .occ 1396, .occ 1399, .occ 1403, .occ 1422, .occ 1428, .occ 1434, .occ 1457, .occ 1458, .occ 1462, .occ 1477, .occ 1524, .occ 1580, .occ 1612, .occ 1626, .occ 1655, .sumGe, .nonneg 10, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchGe 41 (1), .branchLe 19 (0), .branchGe 42 (1), .branchLe 7 (0), .branchLe 31 (0), .branchGe 14 (1)]

def plane484GenLeaf0014Mult : Fin 44 → Nat := ![530, 171, 2084, 238, 2033, 566, 1093, 1761, 1458, 1209, 2922, 1303, 864, 956, 1973, 776, 337, 2103, 199, 437, 103, 649, 158, 317, 923, 1632, 1954, 14, 36, 6072, 1021, 5834, 5335, 6072, 2292, 133, 4936, 6072, 5630, 6072, 5856, 3947, 6072, 12041]

theorem plane484GenLeaf0014 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0014Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0014Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0014Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0014Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 126
  · exact hroot.hOcc 134
  · exact hroot.hOcc 142
  · exact hroot.hOcc 175
  · exact hroot.hOcc 180
  · exact hroot.hOcc 283
  · exact hroot.hOcc 537
  · exact hroot.hOcc 542
  · exact hroot.hOcc 613
  · exact hroot.hOcc 747
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1244
  · exact hroot.hOcc 1351
  · exact hroot.hOcc 1396
  · exact hroot.hOcc 1399
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1434
  · exact hroot.hOcc 1457
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1612
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
