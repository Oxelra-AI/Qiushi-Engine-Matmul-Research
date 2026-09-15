import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0002Refs : Fin 44 → RowRef 713 43 := ![.occ 84, .occ 89, .occ 90, .occ 93, .occ 100, .occ 103, .occ 104, .occ 109, .occ 112, .occ 148, .occ 150, .occ 233, .occ 234, .occ 237, .occ 252, .occ 291, .occ 303, .occ 314, .occ 335, .occ 354, .occ 364, .occ 369, .occ 370, .occ 378, .occ 381, .occ 389, .occ 405, .occ 447, .occ 457, .occ 479, .occ 522, .occ 603, .occ 671, .occ 681, .occ 708, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchLe 16 (0), .branchLe 39 (0), .branchLe 19 (0), .branchLe 10 (0), .branchGe 30 (1)]

def plane490GenLeaf0002Mult : Fin 44 → Nat := ![2044, 667, 1000, 2107, 397, 175, 2611, 276, 1709, 1070, 59, 369, 71, 666, 1859, 1837, 86, 976, 841, 577, 989, 348, 49, 809, 22, 57, 22, 1127, 503, 624, 937, 227, 276, 227, 1312, 3901, 3398, 525, 3674, 2589, 3901, 2042, 2912, 8678]

theorem plane490GenLeaf0002 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0002Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0002Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 148
  · exact hroot.hOcc 150
  · exact hroot.hOcc 233
  · exact hroot.hOcc 234
  · exact hroot.hOcc 237
  · exact hroot.hOcc 252
  · exact hroot.hOcc 291
  · exact hroot.hOcc 303
  · exact hroot.hOcc 314
  · exact hroot.hOcc 335
  · exact hroot.hOcc 354
  · exact hroot.hOcc 364
  · exact hroot.hOcc 369
  · exact hroot.hOcc 370
  · exact hroot.hOcc 378
  · exact hroot.hOcc 381
  · exact hroot.hOcc 389
  · exact hroot.hOcc 405
  · exact hroot.hOcc 447
  · exact hroot.hOcc 457
  · exact hroot.hOcc 479
  · exact hroot.hOcc 522
  · exact hroot.hOcc 603
  · exact hroot.hOcc 671
  · exact hroot.hOcc 681
  · exact hroot.hOcc 708
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30

end QiushiMatmul
