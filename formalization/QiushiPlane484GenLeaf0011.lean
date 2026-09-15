import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0011Refs : Fin 43 → RowRef 1665 43 := ![.occ 127, .occ 128, .occ 132, .occ 134, .occ 145, .occ 290, .occ 491, .occ 492, .occ 493, .occ 495, .occ 535, .occ 1146, .occ 1154, .occ 1164, .occ 1168, .occ 1183, .occ 1213, .occ 1215, .occ 1282, .occ 1305, .occ 1325, .occ 1399, .occ 1503, .occ 1508, .occ 1517, .occ 1523, .occ 1524, .occ 1626, .occ 1657, .occ 1658, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchGe 41 (1), .branchLe 19 (0), .branchLe 42 (0), .branchGe 38 (1), .branchLe 16 (0)]

def plane484GenLeaf0011Mult : Fin 43 → Nat := ![433, 3539, 482, 2516, 3565, 345, 3104, 5536, 4344, 622, 1250, 1660, 1578, 1716, 5538, 396, 616, 2068, 1458, 408, 1830, 370, 2740, 2810, 518, 1806, 1788, 1176, 490, 1582, 12822, 11240, 10766, 7460, 8824, 8682, 5470, 11716, 19330, 11240, 12452, 23128, 8358]

theorem plane484GenLeaf0011 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0011Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0011Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 145
  · exact hroot.hOcc 290
  · exact hroot.hOcc 491
  · exact hroot.hOcc 492
  · exact hroot.hOcc 493
  · exact hroot.hOcc 495
  · exact hroot.hOcc 535
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1305
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1399
  · exact hroot.hOcc 1503
  · exact hroot.hOcc 1508
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1523
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1657
  · exact hroot.hOcc 1658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16

end QiushiMatmul
