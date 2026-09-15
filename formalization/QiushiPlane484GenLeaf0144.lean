import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0144Refs : Fin 43 → RowRef 1665 43 := ![.occ 130, .occ 141, .occ 309, .occ 334, .occ 503, .occ 553, .occ 584, .occ 716, .occ 785, .occ 797, .occ 1140, .occ 1151, .occ 1187, .occ 1216, .occ 1246, .occ 1248, .occ 1283, .occ 1285, .occ 1305, .occ 1413, .occ 1419, .occ 1458, .occ 1521, .occ 1523, .occ 1524, .occ 1601, .occ 1608, .occ 1625, .occ 1653, .occ 1661, .occ 1662, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 39 (1), .branchLe 16 (0), .branchGe 27 (1), .branchLe 24 (0), .branchLe 12 (0), .branchLe 34 (0)]

def plane484GenLeaf0144Mult : Fin 43 → Nat := ![724, 396, 422, 20, 181, 193, 62, 172, 52, 276, 704, 796, 120, 96, 73, 358, 374, 329, 73, 376, 65, 652, 567, 359, 156, 145, 224, 377, 11, 52, 149, 2163, 2014, 2043, 2110, 2014, 1928, 4547, 1938, 328, 1753, 1702, 1922]

theorem plane484GenLeaf0144 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0144Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0144Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0144Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0144Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 130
  · exact hroot.hOcc 141
  · exact hroot.hOcc 309
  · exact hroot.hOcc 334
  · exact hroot.hOcc 503
  · exact hroot.hOcc 553
  · exact hroot.hOcc 584
  · exact hroot.hOcc 716
  · exact hroot.hOcc 785
  · exact hroot.hOcc 797
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1246
  · exact hroot.hOcc 1248
  · exact hroot.hOcc 1283
  · exact hroot.hOcc 1285
  · exact hroot.hOcc 1305
  · exact hroot.hOcc 1413
  · exact hroot.hOcc 1419
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1521
  · exact hroot.hOcc 1523
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1653
  · exact hroot.hOcc 1661
  · exact hroot.hOcc 1662
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34

end QiushiMatmul
