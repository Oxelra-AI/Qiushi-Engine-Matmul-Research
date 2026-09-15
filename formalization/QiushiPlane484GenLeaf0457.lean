import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0457Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 126, .occ 133, .occ 140, .occ 155, .occ 336, .occ 419, .occ 806, .occ 1147, .occ 1188, .occ 1200, .occ 1269, .occ 1306, .occ 1310, .occ 1317, .occ 1344, .occ 1349, .occ 1373, .occ 1394, .occ 1402, .occ 1416, .occ 1462, .occ 1484, .occ 1557, .occ 1625, .occ 1629, .occ 1633, .occ 1645, .occ 1646, .occ 1658, .sumGe, .nonneg 20, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchGe 29 (1), .branchGe 27 (1), .branchLe 8 (0), .branchLe 4 (0), .branchLe 16 (0), .branchLe 22 (0), .branchLe 1 (0), .branchGe 3 (1)]

def plane484GenLeaf0457Mult : Fin 44 → Nat := ![237, 858, 1384, 415, 1578, 367, 457, 1611, 2051, 1290, 327, 546, 522, 2574, 177, 890, 582, 882, 135, 973, 1099, 214, 349, 430, 858, 1315, 96, 1664, 39, 907, 6674, 122, 10089, 6325, 2804, 5816, 5633, 644, 3134, 6674, 6674, 4652, 2202, 7273]

theorem plane484GenLeaf0457 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0457Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0457Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0457Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0457Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 126
  · exact hroot.hOcc 133
  · exact hroot.hOcc 140
  · exact hroot.hOcc 155
  · exact hroot.hOcc 336
  · exact hroot.hOcc 419
  · exact hroot.hOcc 806
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1306
  · exact hroot.hOcc 1310
  · exact hroot.hOcc 1317
  · exact hroot.hOcc 1344
  · exact hroot.hOcc 1349
  · exact hroot.hOcc 1373
  · exact hroot.hOcc 1394
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1416
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1633
  · exact hroot.hOcc 1645
  · exact hroot.hOcc 1646
  · exact hroot.hOcc 1658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
