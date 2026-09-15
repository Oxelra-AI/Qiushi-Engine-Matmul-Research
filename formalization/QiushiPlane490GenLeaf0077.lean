import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0077Refs : Fin 44 → RowRef 713 43 := ![.occ 86, .occ 90, .occ 94, .occ 105, .occ 108, .occ 161, .occ 219, .occ 225, .occ 234, .occ 248, .occ 250, .occ 274, .occ 284, .occ 294, .occ 295, .occ 316, .occ 321, .occ 335, .occ 341, .occ 367, .occ 375, .occ 380, .occ 395, .occ 407, .occ 491, .occ 496, .occ 533, .occ 538, .occ 603, .occ 607, .occ 622, .occ 660, .occ 671, .occ 679, .occ 704, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchLe 22 (0), .branchLe 1 (0), .branchLe 10 (0), .branchLe 14 (0), .branchGe 9 (1)]

def plane490GenLeaf0077Mult : Fin 44 → Nat := ![2446, 1605, 2461, 7714, 2611, 4635, 967, 3152, 38, 599, 3160, 1515, 2080, 2201, 164, 668, 2227, 2327, 2597, 12, 1613, 1339, 2310, 1482, 15, 379, 576, 1955, 891, 287, 3542, 274, 683, 955, 1572, 8313, 24832, 7737, 6798, 5690, 8026, 6700, 7737, 13416]

theorem plane490GenLeaf0077 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0077Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0077Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0077Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0077Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 90
  · exact hroot.hOcc 94
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 161
  · exact hroot.hOcc 219
  · exact hroot.hOcc 225
  · exact hroot.hOcc 234
  · exact hroot.hOcc 248
  · exact hroot.hOcc 250
  · exact hroot.hOcc 274
  · exact hroot.hOcc 284
  · exact hroot.hOcc 294
  · exact hroot.hOcc 295
  · exact hroot.hOcc 316
  · exact hroot.hOcc 321
  · exact hroot.hOcc 335
  · exact hroot.hOcc 341
  · exact hroot.hOcc 367
  · exact hroot.hOcc 375
  · exact hroot.hOcc 380
  · exact hroot.hOcc 395
  · exact hroot.hOcc 407
  · exact hroot.hOcc 491
  · exact hroot.hOcc 496
  · exact hroot.hOcc 533
  · exact hroot.hOcc 538
  · exact hroot.hOcc 603
  · exact hroot.hOcc 607
  · exact hroot.hOcc 622
  · exact hroot.hOcc 660
  · exact hroot.hOcc 671
  · exact hroot.hOcc 679
  · exact hroot.hOcc 704
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
