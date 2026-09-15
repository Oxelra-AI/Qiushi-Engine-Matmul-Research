import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0021Refs : Fin 44 → RowRef 713 43 := ![.occ 86, .occ 94, .occ 95, .occ 99, .occ 110, .occ 122, .occ 134, .occ 189, .occ 229, .occ 283, .occ 314, .occ 324, .occ 335, .occ 364, .occ 390, .occ 397, .occ 414, .occ 489, .occ 491, .occ 500, .occ 501, .occ 503, .occ 524, .occ 525, .occ 532, .occ 534, .occ 599, .occ 607, .occ 617, .occ 665, .occ 686, .occ 692, .occ 695, .occ 710, .sumGe, .nonneg 24, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchGe 16 (1), .branchGe 15 (1), .branchLe 32 (0), .branchLe 3 (0), .branchGe 42 (1)]

def plane490GenLeaf0021Mult : Fin 44 → Nat := ![8727, 22236, 23869, 214, 1746, 4400, 5545, 7945, 2912, 25930, 2936, 3859, 2813, 18912, 11458, 4886, 14267, 3233, 195, 3594, 5509, 12447, 998, 3122, 4200, 2668, 2302, 442, 1371, 10927, 1049, 1436, 7794, 1797, 34672, 8056, 25004, 22917, 29130, 55321, 33928, 25597, 16777, 99791]

theorem plane490GenLeaf0021 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0021Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0021Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0021Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0021Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 110
  · exact hroot.hOcc 122
  · exact hroot.hOcc 134
  · exact hroot.hOcc 189
  · exact hroot.hOcc 229
  · exact hroot.hOcc 283
  · exact hroot.hOcc 314
  · exact hroot.hOcc 324
  · exact hroot.hOcc 335
  · exact hroot.hOcc 364
  · exact hroot.hOcc 390
  · exact hroot.hOcc 397
  · exact hroot.hOcc 414
  · exact hroot.hOcc 489
  · exact hroot.hOcc 491
  · exact hroot.hOcc 500
  · exact hroot.hOcc 501
  · exact hroot.hOcc 503
  · exact hroot.hOcc 524
  · exact hroot.hOcc 525
  · exact hroot.hOcc 532
  · exact hroot.hOcc 534
  · exact hroot.hOcc 599
  · exact hroot.hOcc 607
  · exact hroot.hOcc 617
  · exact hroot.hOcc 665
  · exact hroot.hOcc 686
  · exact hroot.hOcc 692
  · exact hroot.hOcc 695
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
