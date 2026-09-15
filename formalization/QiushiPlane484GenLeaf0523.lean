import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0523Refs : Fin 44 → RowRef 1665 43 := ![.occ 135, .occ 138, .occ 381, .occ 390, .occ 399, .occ 568, .occ 573, .occ 596, .occ 597, .occ 676, .occ 713, .occ 815, .occ 1159, .occ 1188, .occ 1206, .occ 1297, .occ 1298, .occ 1299, .occ 1358, .occ 1378, .occ 1422, .occ 1423, .occ 1429, .occ 1447, .occ 1471, .occ 1478, .occ 1623, .occ 1624, .occ 1633, .sumGe, .nonneg 0, .nonneg 2, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchGe 34 (1), .branchLe 9 (0), .branchGe 18 (1), .branchLe 1 (0), .branchLe 12 (0), .branchLe 23 (0), .branchGe 36 (1)]

def plane484GenLeaf0523Mult : Fin 44 → Nat := ![55, 112, 84, 5, 9, 24, 60, 78, 66, 11, 15, 9, 116, 95, 26, 7, 63, 11, 21, 18, 14, 20, 16, 45, 14, 13, 14, 12, 5, 160, 3, 107, 541, 256, 28, 2, 53, 512, 160, 285, 107, 99, 20, 356]

theorem plane484GenLeaf0523 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0523Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0523Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0523Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0523Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 381
  · exact hroot.hOcc 390
  · exact hroot.hOcc 399
  · exact hroot.hOcc 568
  · exact hroot.hOcc 573
  · exact hroot.hOcc 596
  · exact hroot.hOcc 597
  · exact hroot.hOcc 676
  · exact hroot.hOcc 713
  · exact hroot.hOcc 815
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1299
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1378
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1423
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1447
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1633
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36

end QiushiMatmul
