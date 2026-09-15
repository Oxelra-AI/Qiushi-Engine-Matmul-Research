import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0567Refs : Fin 42 → RowRef 1665 43 := ![.occ 125, .occ 127, .occ 133, .occ 198, .occ 199, .occ 330, .occ 366, .occ 383, .occ 423, .occ 572, .occ 640, .occ 696, .occ 702, .occ 858, .occ 962, .occ 1082, .occ 1145, .occ 1160, .occ 1222, .occ 1237, .occ 1241, .occ 1265, .occ 1277, .occ 1293, .occ 1324, .occ 1478, .occ 1542, .occ 1548, .occ 1590, .occ 1613, .occ 1637, .occ 1640, .occ 1662, .sumGe, .nonneg 21, .nonneg 24, .branchGe 15 (1), .branchGe 35 (1), .branchGe 25 (1), .branchGe 29 (1), .branchLe 32 (0), .branchGe 4 (1)]

def plane484GenLeaf0567Mult : Fin 42 → Nat := ![28, 2, 102, 24, 4, 1, 4, 68, 13, 24, 20, 1, 100, 4, 1, 94, 41, 1, 4, 33, 36, 4, 1, 19, 3, 4, 5, 51, 2, 88, 2, 35, 16, 110, 171, 8, 233, 252, 527, 444, 110, 455]

theorem plane484GenLeaf0567 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0567Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0567Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0567Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0567Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 133
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · exact hroot.hOcc 330
  · exact hroot.hOcc 366
  · exact hroot.hOcc 383
  · exact hroot.hOcc 423
  · exact hroot.hOcc 572
  · exact hroot.hOcc 640
  · exact hroot.hOcc 696
  · exact hroot.hOcc 702
  · exact hroot.hOcc 858
  · exact hroot.hOcc 962
  · exact hroot.hOcc 1082
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1237
  · exact hroot.hOcc 1241
  · exact hroot.hOcc 1265
  · exact hroot.hOcc 1277
  · exact hroot.hOcc 1293
  · exact hroot.hOcc 1324
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1542
  · exact hroot.hOcc 1548
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1613
  · exact hroot.hOcc 1637
  · exact hroot.hOcc 1640
  · exact hroot.hOcc 1662
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
