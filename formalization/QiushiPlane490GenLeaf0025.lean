import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0025Refs : Fin 44 → RowRef 713 43 := ![.occ 84, .occ 85, .occ 89, .occ 94, .occ 95, .occ 102, .occ 103, .occ 111, .occ 127, .occ 150, .occ 153, .occ 179, .occ 269, .occ 271, .occ 291, .occ 295, .occ 303, .occ 316, .occ 333, .occ 354, .occ 364, .occ 373, .occ 387, .occ 402, .occ 475, .occ 518, .occ 534, .occ 604, .occ 632, .occ 650, .occ 653, .occ 664, .occ 666, .occ 672, .occ 692, .sumGe, .nonneg 29, .branchLe 4 (0), .branchLe 23 (0), .branchGe 16 (1), .branchGe 15 (1), .branchGe 32 (1), .branchLe 20 (0), .branchGe 33 (1)]

def plane490GenLeaf0025Mult : Fin 44 → Nat := ![44, 71, 18, 97, 129, 29, 73, 61, 58, 1, 20, 19, 11, 40, 46, 18, 3, 59, 96, 58, 57, 14, 54, 16, 25, 9, 26, 49, 40, 10, 37, 2, 33, 5, 1, 134, 70, 29, 134, 381, 173, 299, 133, 393]

theorem plane490GenLeaf0025 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0025Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0025Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0025Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0025Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 111
  · exact hroot.hOcc 127
  · exact hroot.hOcc 150
  · exact hroot.hOcc 153
  · exact hroot.hOcc 179
  · exact hroot.hOcc 269
  · exact hroot.hOcc 271
  · exact hroot.hOcc 291
  · exact hroot.hOcc 295
  · exact hroot.hOcc 303
  · exact hroot.hOcc 316
  · exact hroot.hOcc 333
  · exact hroot.hOcc 354
  · exact hroot.hOcc 364
  · exact hroot.hOcc 373
  · exact hroot.hOcc 387
  · exact hroot.hOcc 402
  · exact hroot.hOcc 475
  · exact hroot.hOcc 518
  · exact hroot.hOcc 534
  · exact hroot.hOcc 604
  · exact hroot.hOcc 632
  · exact hroot.hOcc 650
  · exact hroot.hOcc 653
  · exact hroot.hOcc 664
  · exact hroot.hOcc 666
  · exact hroot.hOcc 672
  · exact hroot.hOcc 692
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
