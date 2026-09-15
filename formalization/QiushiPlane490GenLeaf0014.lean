import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0014Refs : Fin 36 → RowRef 713 43 := ![.occ 106, .occ 117, .occ 131, .occ 198, .occ 202, .occ 238, .occ 268, .occ 284, .occ 314, .occ 323, .occ 335, .occ 340, .occ 354, .occ 371, .occ 375, .occ 415, .occ 419, .occ 449, .occ 495, .occ 501, .occ 522, .occ 591, .occ 613, .occ 649, .occ 704, .sumGe, .nonneg 14, .nonneg 25, .nonneg 28, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchLe 16 (0), .branchGe 39 (1), .branchGe 17 (1), .branchGe 8 (1)]

def plane490GenLeaf0014Mult : Fin 36 → Nat := ![7, 3, 5, 2, 5, 6, 1, 8, 7, 1, 15, 10, 2, 2, 4, 9, 7, 8, 4, 2, 1, 8, 1, 1, 2, 17, 6, 3, 2, 14, 12, 17, 15, 32, 55, 58]

theorem plane490GenLeaf0014 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0014Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0014Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0014Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0014Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 106
  · exact hroot.hOcc 117
  · exact hroot.hOcc 131
  · exact hroot.hOcc 198
  · exact hroot.hOcc 202
  · exact hroot.hOcc 238
  · exact hroot.hOcc 268
  · exact hroot.hOcc 284
  · exact hroot.hOcc 314
  · exact hroot.hOcc 323
  · exact hroot.hOcc 335
  · exact hroot.hOcc 340
  · exact hroot.hOcc 354
  · exact hroot.hOcc 371
  · exact hroot.hOcc 375
  · exact hroot.hOcc 415
  · exact hroot.hOcc 419
  · exact hroot.hOcc 449
  · exact hroot.hOcc 495
  · exact hroot.hOcc 501
  · exact hroot.hOcc 522
  · exact hroot.hOcc 591
  · exact hroot.hOcc 613
  · exact hroot.hOcc 649
  · exact hroot.hOcc 704
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
