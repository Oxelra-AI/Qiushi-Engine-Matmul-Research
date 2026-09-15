import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0550Refs : Fin 43 → RowRef 1665 43 := ![.occ 128, .occ 133, .occ 149, .occ 170, .occ 250, .occ 292, .occ 377, .occ 581, .occ 664, .occ 675, .occ 1140, .occ 1158, .occ 1173, .occ 1179, .occ 1200, .occ 1205, .occ 1208, .occ 1324, .occ 1346, .occ 1357, .occ 1467, .occ 1472, .occ 1484, .occ 1486, .occ 1492, .occ 1590, .occ 1597, .occ 1615, .occ 1621, .occ 1624, .occ 1646, .sumGe, .nonneg 18, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchGe 1 (1), .branchLe 11 (0), .branchGe 32 (1), .branchLe 20 (0), .branchLe 4 (0)]

def plane484GenLeaf0550Mult : Fin 43 → Nat := ![10546, 11568, 1481, 8192, 545, 6952, 10296, 9952, 6854, 2503, 355, 5605, 5667, 598, 3873, 743, 13646, 763, 1363, 7315, 131, 2848, 9948, 4999, 2817, 545, 730, 2860, 1492, 664, 1966, 23603, 7857, 60640, 40837, 7857, 11685, 41872, 28059, 19730, 40563, 11804, 20743]

theorem plane484GenLeaf0550 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0550Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0550Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0550Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0550Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 128
  · exact hroot.hOcc 133
  · exact hroot.hOcc 149
  · exact hroot.hOcc 170
  · exact hroot.hOcc 250
  · exact hroot.hOcc 292
  · exact hroot.hOcc 377
  · exact hroot.hOcc 581
  · exact hroot.hOcc 664
  · exact hroot.hOcc 675
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1324
  · exact hroot.hOcc 1346
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1621
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1646
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (11 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
