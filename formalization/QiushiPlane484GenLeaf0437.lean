import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0437Refs : Fin 44 → RowRef 1665 43 := ![.occ 125, .occ 128, .occ 138, .occ 527, .occ 675, .occ 746, .occ 763, .occ 958, .occ 998, .occ 1145, .occ 1150, .occ 1188, .occ 1244, .occ 1267, .occ 1281, .occ 1282, .occ 1304, .occ 1318, .occ 1333, .occ 1340, .occ 1350, .occ 1388, .occ 1392, .occ 1433, .occ 1438, .occ 1458, .occ 1470, .occ 1477, .occ 1580, .occ 1633, .sumGe, .nonneg 18, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchLe 29 (0), .branchLe 23 (0), .branchGe 19 (1), .branchLe 31 (0), .branchLe 20 (0), .branchGe 38 (1), .branchLe 17 (0), .branchLe 28 (0)]

def plane484GenLeaf0437Mult : Fin 44 → Nat := ![58940, 73976, 189480, 78592, 49092, 6044, 47504, 119067, 79250, 26334, 99620, 2022, 13826, 11783, 62514, 7676, 48033, 28539, 1202, 99341, 68231, 5159, 56002, 7161, 16032, 51784, 37328, 49762, 31294, 66988, 343764, 24088, 256668, 233368, 276776, 343764, 343764, 19480, 437896, 68484, 292800, 368224, 343764, 343764]

theorem plane484GenLeaf0437 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0437Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0437Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0437Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0437Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 138
  · exact hroot.hOcc 527
  · exact hroot.hOcc 675
  · exact hroot.hOcc 746
  · exact hroot.hOcc 763
  · exact hroot.hOcc 958
  · exact hroot.hOcc 998
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1244
  · exact hroot.hOcc 1267
  · exact hroot.hOcc 1281
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1304
  · exact hroot.hOcc 1318
  · exact hroot.hOcc 1333
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1438
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1633
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
