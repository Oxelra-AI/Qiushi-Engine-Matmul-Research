import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0036Refs : Fin 44 → RowRef 1665 43 := ![.occ 134, .occ 141, .occ 210, .occ 211, .occ 370, .occ 611, .occ 622, .occ 801, .occ 833, .occ 886, .occ 1147, .occ 1170, .occ 1213, .occ 1221, .occ 1274, .occ 1278, .occ 1313, .occ 1367, .occ 1378, .occ 1422, .occ 1492, .occ 1527, .occ 1597, .occ 1607, .occ 1608, .occ 1618, .occ 1624, .occ 1627, .occ 1648, .occ 1653, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchGe 25 (1), .branchLe 33 (0), .branchLe 16 (0), .branchLe 10 (0), .branchLe 21 (0), .branchGe 28 (1)]

def plane484GenLeaf0036Mult : Fin 44 → Nat := ![5597, 1756, 2957, 2244, 4340, 1278, 1672, 202, 4834, 1610, 1516, 1435, 5264, 1931, 108, 3222, 2144, 2900, 88, 1334, 63, 1260, 1705, 2181, 5817, 1315, 682, 601, 2375, 19, 13186, 8862, 9232, 13104, 11852, 11815, 3788, 25696, 30593, 8630, 2417, 7333, 5830, 26311]

theorem plane484GenLeaf0036 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0036Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0036Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0036Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0036Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 134
  · exact hroot.hOcc 141
  · exact hroot.hOcc 210
  · exact hroot.hOcc 211
  · exact hroot.hOcc 370
  · exact hroot.hOcc 611
  · exact hroot.hOcc 622
  · exact hroot.hOcc 801
  · exact hroot.hOcc 833
  · exact hroot.hOcc 886
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1221
  · exact hroot.hOcc 1274
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1313
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1378
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1527
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1627
  · exact hroot.hOcc 1648
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
