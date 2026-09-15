import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0530Refs : Fin 43 → RowRef 1665 43 := ![.occ 132, .occ 240, .occ 277, .occ 295, .occ 594, .occ 1205, .occ 1208, .occ 1222, .occ 1224, .occ 1258, .occ 1260, .occ 1270, .occ 1277, .occ 1292, .occ 1329, .occ 1343, .occ 1346, .occ 1371, .occ 1372, .occ 1394, .occ 1402, .occ 1403, .occ 1417, .occ 1467, .occ 1484, .occ 1486, .occ 1505, .occ 1563, .occ 1659, .sumGe, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchLe 1 (0), .branchLe 0 (0), .branchLe 19 (0), .branchLe 2 (0), .branchLe 14 (0), .branchLe 40 (0), .branchLe 3 (0), .branchLe 4 (0)]

def plane484GenLeaf0530Mult : Fin 43 → Nat := ![49, 24, 46, 121, 96, 95, 62, 20, 62, 22, 52, 21, 86, 15, 66, 56, 76, 45, 19, 18, 34, 82, 18, 17, 44, 14, 5, 41, 23, 314, 279, 436, 124, 250, 793, 140, 242, 300, 256, 314, 314, 173, 299]

theorem plane484GenLeaf0530 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0530Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0530Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0530Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0530Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 132
  · exact hroot.hOcc 240
  · exact hroot.hOcc 277
  · exact hroot.hOcc 295
  · exact hroot.hOcc 594
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1224
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1277
  · exact hroot.hOcc 1292
  · exact hroot.hOcc 1329
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1346
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1372
  · exact hroot.hOcc 1394
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1417
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1563
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
