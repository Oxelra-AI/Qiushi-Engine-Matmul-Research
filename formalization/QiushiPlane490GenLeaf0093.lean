import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0093Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 90, .occ 93, .occ 95, .occ 105, .occ 106, .occ 108, .occ 112, .occ 113, .occ 117, .occ 137, .occ 145, .occ 170, .occ 186, .occ 204, .occ 239, .occ 252, .occ 295, .occ 297, .occ 322, .occ 336, .occ 364, .occ 365, .occ 389, .occ 397, .occ 427, .occ 453, .occ 466, .occ 475, .occ 479, .occ 517, .occ 632, .occ 653, .occ 655, .occ 667, .occ 671, .occ 690, .occ 701, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchGe 22 (1), .branchGe 3 (1)]

def plane490GenLeaf0093Mult : Fin 44 → Nat := ![1529, 2220, 649, 84, 1611, 120, 1829, 419, 1025, 498, 1579, 1426, 1352, 18, 151, 1148, 711, 695, 236, 237, 98, 28, 419, 529, 239, 353, 1000, 514, 428, 781, 111, 1011, 143, 752, 133, 39, 177, 181, 2540, 5085, 1788, 1154, 7294, 9077]

theorem plane490GenLeaf0093 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0093Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0093Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0093Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0093Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 117
  · exact hroot.hOcc 137
  · exact hroot.hOcc 145
  · exact hroot.hOcc 170
  · exact hroot.hOcc 186
  · exact hroot.hOcc 204
  · exact hroot.hOcc 239
  · exact hroot.hOcc 252
  · exact hroot.hOcc 295
  · exact hroot.hOcc 297
  · exact hroot.hOcc 322
  · exact hroot.hOcc 336
  · exact hroot.hOcc 364
  · exact hroot.hOcc 365
  · exact hroot.hOcc 389
  · exact hroot.hOcc 397
  · exact hroot.hOcc 427
  · exact hroot.hOcc 453
  · exact hroot.hOcc 466
  · exact hroot.hOcc 475
  · exact hroot.hOcc 479
  · exact hroot.hOcc 517
  · exact hroot.hOcc 632
  · exact hroot.hOcc 653
  · exact hroot.hOcc 655
  · exact hroot.hOcc 667
  · exact hroot.hOcc 671
  · exact hroot.hOcc 690
  · exact hroot.hOcc 701
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
