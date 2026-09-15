import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0057Refs : Fin 44 → RowRef 713 43 := ![.occ 90, .occ 150, .occ 163, .occ 171, .occ 191, .occ 198, .occ 219, .occ 233, .occ 247, .occ 274, .occ 284, .occ 291, .occ 302, .occ 307, .occ 316, .occ 336, .occ 375, .occ 378, .occ 421, .occ 457, .occ 460, .occ 461, .occ 472, .occ 480, .occ 491, .occ 522, .occ 599, .occ 609, .occ 610, .occ 649, .occ 674, .occ 694, .occ 704, .sumGe, .nonneg 27, .nonneg 40, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchGe 30 (1), .branchGe 6 (1), .branchLe 22 (0), .branchGe 39 (1), .branchGe 31 (1)]

def plane490GenLeaf0057Mult : Fin 44 → Nat := ![351, 5, 185, 222, 883, 34, 211, 243, 207, 55, 99, 79, 350, 154, 207, 583, 252, 38, 128, 54, 187, 370, 282, 163, 144, 326, 172, 5, 19, 39, 44, 247, 10, 883, 459, 491, 601, 749, 2743, 2991, 687, 577, 972, 1045]

theorem plane490GenLeaf0057 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0057Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0057Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0057Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0057Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 150
  · exact hroot.hOcc 163
  · exact hroot.hOcc 171
  · exact hroot.hOcc 191
  · exact hroot.hOcc 198
  · exact hroot.hOcc 219
  · exact hroot.hOcc 233
  · exact hroot.hOcc 247
  · exact hroot.hOcc 274
  · exact hroot.hOcc 284
  · exact hroot.hOcc 291
  · exact hroot.hOcc 302
  · exact hroot.hOcc 307
  · exact hroot.hOcc 316
  · exact hroot.hOcc 336
  · exact hroot.hOcc 375
  · exact hroot.hOcc 378
  · exact hroot.hOcc 421
  · exact hroot.hOcc 457
  · exact hroot.hOcc 460
  · exact hroot.hOcc 461
  · exact hroot.hOcc 472
  · exact hroot.hOcc 480
  · exact hroot.hOcc 491
  · exact hroot.hOcc 522
  · exact hroot.hOcc 599
  · exact hroot.hOcc 609
  · exact hroot.hOcc 610
  · exact hroot.hOcc 649
  · exact hroot.hOcc 674
  · exact hroot.hOcc 694
  · exact hroot.hOcc 704
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31

end QiushiMatmul
