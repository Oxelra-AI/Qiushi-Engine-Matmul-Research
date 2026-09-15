import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0193Refs : Fin 41 → RowRef 1665 43 := ![.occ 120, .occ 124, .occ 129, .occ 132, .occ 196, .occ 210, .occ 220, .occ 283, .occ 422, .occ 470, .occ 473, .occ 1023, .occ 1154, .occ 1173, .occ 1258, .occ 1328, .occ 1341, .occ 1349, .occ 1352, .occ 1381, .occ 1478, .occ 1492, .occ 1496, .occ 1516, .occ 1529, .occ 1535, .occ 1622, .occ 1630, .occ 1663, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchLe 1 (0), .branchGe 5 (1), .branchGe 22 (1), .branchLe 19 (0), .branchLe 39 (0)]

def plane484GenLeaf0193Mult : Fin 41 → Nat := ![1335, 668, 132, 1183, 1064, 355, 256, 612, 771, 376, 529, 769, 796, 128, 1866, 128, 740, 116, 394, 298, 813, 143, 1361, 869, 44, 68, 64, 227, 128, 2970, 2495, 798, 5545, 3920, 143, 746, 522, 8160, 4971, 2970, 2970]

theorem plane484GenLeaf0193 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0193Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0193Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0193Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0193Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 196
  · exact hroot.hOcc 210
  · exact hroot.hOcc 220
  · exact hroot.hOcc 283
  · exact hroot.hOcc 422
  · exact hroot.hOcc 470
  · exact hroot.hOcc 473
  · exact hroot.hOcc 1023
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1328
  · exact hroot.hOcc 1341
  · exact hroot.hOcc 1349
  · exact hroot.hOcc 1352
  · exact hroot.hOcc 1381
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1535
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39

end QiushiMatmul
