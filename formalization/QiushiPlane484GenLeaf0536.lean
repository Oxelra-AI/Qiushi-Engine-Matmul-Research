import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0536Refs : Fin 43 → RowRef 1665 43 := ![.occ 133, .occ 138, .occ 186, .occ 196, .occ 212, .occ 295, .occ 513, .occ 1183, .occ 1186, .occ 1187, .occ 1188, .occ 1208, .occ 1221, .occ 1237, .occ 1291, .occ 1293, .occ 1312, .occ 1348, .occ 1358, .occ 1371, .occ 1421, .occ 1444, .occ 1450, .occ 1519, .occ 1542, .occ 1562, .occ 1619, .occ 1629, .occ 1638, .occ 1642, .sumGe, .nonneg 25, .branchGe 15 (1), .branchGe 35 (1), .branchLe 26 (0), .branchGe 30 (1), .branchLe 1 (0), .branchLe 0 (0), .branchGe 19 (1), .branchLe 6 (0), .branchLe 20 (0), .branchLe 13 (0), .branchLe 37 (0)]

def plane484GenLeaf0536Mult : Fin 43 → Nat := ![1721, 2447, 1233, 2802, 1472, 5705, 1202, 1388, 1144, 657, 1622, 1328, 1171, 372, 544, 2025, 1732, 3829, 32, 318, 1251, 2638, 468, 220, 1109, 126, 70, 2891, 2509, 308, 10075, 2715, 9499, 14370, 7320, 20021, 4135, 9973, 10390, 10075, 8617, 9697, 10075]

theorem plane484GenLeaf0536 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0536Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0536Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0536Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0536Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 186
  · exact hroot.hOcc 196
  · exact hroot.hOcc 212
  · exact hroot.hOcc 295
  · exact hroot.hOcc 513
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1221
  · exact hroot.hOcc 1237
  · exact hroot.hOcc 1291
  · exact hroot.hOcc 1293
  · exact hroot.hOcc 1312
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1421
  · exact hroot.hOcc 1444
  · exact hroot.hOcc 1450
  · exact hroot.hOcc 1519
  · exact hroot.hOcc 1542
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1642
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37

end QiushiMatmul
