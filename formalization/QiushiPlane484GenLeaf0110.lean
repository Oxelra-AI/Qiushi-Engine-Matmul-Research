import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0110Refs : Fin 43 → RowRef 1665 43 := ![.occ 129, .occ 130, .occ 131, .occ 179, .occ 180, .occ 202, .occ 290, .occ 429, .occ 653, .occ 707, .occ 852, .occ 901, .occ 922, .occ 980, .occ 993, .occ 1141, .occ 1151, .occ 1261, .occ 1278, .occ 1294, .occ 1298, .occ 1342, .occ 1438, .occ 1444, .occ 1472, .occ 1477, .occ 1478, .occ 1515, .occ 1538, .occ 1539, .occ 1549, .occ 1597, .occ 1661, .sumGe, .nonneg 1, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchGe 36 (1), .branchLe 26 (0), .branchGe 19 (1), .branchLe 30 (0)]

def plane484GenLeaf0110Mult : Fin 43 → Nat := ![36, 457, 275, 27, 222, 63, 36, 132, 175, 60, 5, 242, 429, 36, 597, 92, 288, 68, 36, 366, 59, 18, 210, 142, 122, 247, 143, 86, 61, 41, 92, 285, 77, 941, 263, 515, 719, 592, 3158, 2321, 515, 2204, 941]

theorem plane484GenLeaf0110 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0110Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0110Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0110Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0110Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 179
  · exact hroot.hOcc 180
  · exact hroot.hOcc 202
  · exact hroot.hOcc 290
  · exact hroot.hOcc 429
  · exact hroot.hOcc 653
  · exact hroot.hOcc 707
  · exact hroot.hOcc 852
  · exact hroot.hOcc 901
  · exact hroot.hOcc 922
  · exact hroot.hOcc 980
  · exact hroot.hOcc 993
  · exact hroot.hOcc 1141
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1261
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1294
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1438
  · exact hroot.hOcc 1444
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1515
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1539
  · exact hroot.hOcc 1549
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30

end QiushiMatmul
