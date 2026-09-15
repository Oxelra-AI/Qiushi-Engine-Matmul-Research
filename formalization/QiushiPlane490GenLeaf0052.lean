import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0052Refs : Fin 44 → RowRef 713 43 := ![.occ 91, .occ 94, .occ 116, .occ 135, .occ 154, .occ 177, .occ 236, .occ 237, .occ 238, .occ 245, .occ 277, .occ 290, .occ 302, .occ 335, .occ 336, .occ 362, .occ 364, .occ 375, .occ 391, .occ 395, .occ 413, .occ 416, .occ 425, .occ 430, .occ 460, .occ 501, .occ 520, .occ 563, .occ 599, .occ 601, .occ 608, .occ 640, .occ 647, .occ 676, .occ 709, .occ 711, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchGe 28 (1), .branchGe 39 (1), .branchGe 19 (1)]

def plane490GenLeaf0052Mult : Fin 44 → Nat := ![149, 350, 6, 408, 229, 48, 371, 44, 64, 536, 88, 36, 70, 486, 14, 170, 223, 149, 130, 42, 318, 10, 19, 125, 157, 28, 36, 365, 42, 22, 2, 94, 36, 64, 28, 80, 672, 520, 608, 128, 435, 2594, 544, 1952]

theorem plane490GenLeaf0052 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0052Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0052Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0052Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0052Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 116
  · exact hroot.hOcc 135
  · exact hroot.hOcc 154
  · exact hroot.hOcc 177
  · exact hroot.hOcc 236
  · exact hroot.hOcc 237
  · exact hroot.hOcc 238
  · exact hroot.hOcc 245
  · exact hroot.hOcc 277
  · exact hroot.hOcc 290
  · exact hroot.hOcc 302
  · exact hroot.hOcc 335
  · exact hroot.hOcc 336
  · exact hroot.hOcc 362
  · exact hroot.hOcc 364
  · exact hroot.hOcc 375
  · exact hroot.hOcc 391
  · exact hroot.hOcc 395
  · exact hroot.hOcc 413
  · exact hroot.hOcc 416
  · exact hroot.hOcc 425
  · exact hroot.hOcc 430
  · exact hroot.hOcc 460
  · exact hroot.hOcc 501
  · exact hroot.hOcc 520
  · exact hroot.hOcc 563
  · exact hroot.hOcc 599
  · exact hroot.hOcc 601
  · exact hroot.hOcc 608
  · exact hroot.hOcc 640
  · exact hroot.hOcc 647
  · exact hroot.hOcc 676
  · exact hroot.hOcc 709
  · exact hroot.hOcc 711
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19

end QiushiMatmul
