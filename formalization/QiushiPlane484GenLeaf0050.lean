import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0050Refs : Fin 42 → RowRef 1665 43 := ![.occ 128, .occ 134, .occ 139, .occ 143, .occ 337, .occ 381, .occ 707, .occ 755, .occ 845, .occ 847, .occ 1174, .occ 1200, .occ 1223, .occ 1234, .occ 1263, .occ 1264, .occ 1342, .occ 1367, .occ 1369, .occ 1422, .occ 1430, .occ 1470, .occ 1481, .occ 1500, .occ 1502, .occ 1503, .occ 1509, .occ 1552, .occ 1609, .occ 1610, .occ 1626, .occ 1647, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchGe 17 (1), .branchLe 7 (0), .branchGe 18 (1), .branchLe 41 (0)]

def plane484GenLeaf0050Mult : Fin 42 → Nat := ![82264, 127827, 38897, 42230, 81020, 4256, 331252, 104536, 21558, 53450, 187566, 20582, 51968, 34046, 72867, 57883, 35466, 19861, 62911, 40312, 136106, 84590, 40060, 16063, 15573, 93682, 46492, 6738, 13908, 18860, 157124, 42204, 521144, 500562, 376068, 481084, 521144, 521144, 368636, 202652, 1127878, 488376]

theorem plane484GenLeaf0050 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0050Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0050Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0050Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0050Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 128
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 143
  · exact hroot.hOcc 337
  · exact hroot.hOcc 381
  · exact hroot.hOcc 707
  · exact hroot.hOcc 755
  · exact hroot.hOcc 845
  · exact hroot.hOcc 847
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1223
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1263
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1369
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1500
  · exact hroot.hOcc 1502
  · exact hroot.hOcc 1503
  · exact hroot.hOcc 1509
  · exact hroot.hOcc 1552
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1647
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41

end QiushiMatmul
