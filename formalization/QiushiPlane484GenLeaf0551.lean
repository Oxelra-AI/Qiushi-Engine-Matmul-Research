import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0551Refs : Fin 43 → RowRef 1665 43 := ![.occ 127, .occ 133, .occ 138, .occ 140, .occ 170, .occ 199, .occ 292, .occ 388, .occ 464, .occ 471, .occ 693, .occ 911, .occ 988, .occ 1081, .occ 1140, .occ 1158, .occ 1160, .occ 1208, .occ 1297, .occ 1300, .occ 1484, .occ 1486, .occ 1496, .occ 1540, .occ 1573, .occ 1597, .occ 1615, .occ 1619, .occ 1629, .occ 1638, .sumGe, .nonneg 7, .nonneg 17, .nonneg 26, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchGe 30 (1), .branchGe 1 (1), .branchLe 11 (0), .branchGe 32 (1), .branchLe 20 (0), .branchGe 4 (1)]

def plane484GenLeaf0551Mult : Fin 43 → Nat := ![249, 118, 18, 60, 288, 20, 165, 70, 31, 120, 116, 34, 83, 115, 25, 65, 114, 37, 23, 86, 59, 53, 49, 23, 115, 34, 127, 8, 6, 20, 314, 25, 4, 66, 968, 750, 170, 799, 215, 294, 823, 138, 868]

theorem plane484GenLeaf0551 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0551Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0551Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0551Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0551Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 127
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 170
  · exact hroot.hOcc 199
  · exact hroot.hOcc 292
  · exact hroot.hOcc 388
  · exact hroot.hOcc 464
  · exact hroot.hOcc 471
  · exact hroot.hOcc 693
  · exact hroot.hOcc 911
  · exact hroot.hOcc 988
  · exact hroot.hOcc 1081
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1300
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1540
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1638
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (11 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
