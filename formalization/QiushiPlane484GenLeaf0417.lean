import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0417Refs : Fin 40 → RowRef 1665 43 := ![.occ 127, .occ 129, .occ 136, .occ 137, .occ 143, .occ 165, .occ 180, .occ 233, .occ 634, .occ 743, .occ 779, .occ 841, .occ 981, .occ 1134, .occ 1172, .occ 1183, .occ 1188, .occ 1260, .occ 1274, .occ 1376, .occ 1412, .occ 1462, .occ 1508, .occ 1510, .occ 1512, .occ 1514, .occ 1608, .occ 1638, .occ 1661, .sumGe, .nonneg 6, .nonneg 10, .nonneg 11, .nonneg 19, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchGe 31 (1), .branchLe 29 (0), .branchGe 14 (1)]

def plane484GenLeaf0417Mult : Fin 40 → Nat := ![2823, 2310, 1307, 204, 3102, 1692, 204, 784, 789, 123, 18, 437, 130, 649, 199, 1619, 5, 18, 872, 575, 1359, 359, 871, 709, 237, 61, 593, 75, 80, 3182, 9292, 1619, 204, 370, 2467, 3983, 14125, 5464, 3182, 12029]

theorem plane484GenLeaf0417 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0417Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0417Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0417Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0417Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 143
  · exact hroot.hOcc 165
  · exact hroot.hOcc 180
  · exact hroot.hOcc 233
  · exact hroot.hOcc 634
  · exact hroot.hOcc 743
  · exact hroot.hOcc 779
  · exact hroot.hOcc 841
  · exact hroot.hOcc 981
  · exact hroot.hOcc 1134
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1274
  · exact hroot.hOcc 1376
  · exact hroot.hOcc 1412
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1508
  · exact hroot.hOcc 1510
  · exact hroot.hOcc 1512
  · exact hroot.hOcc 1514
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
