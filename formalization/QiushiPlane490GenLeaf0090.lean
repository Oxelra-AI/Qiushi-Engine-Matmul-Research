import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0090Refs : Fin 44 → RowRef 713 43 := ![.occ 84, .occ 86, .occ 93, .occ 105, .occ 108, .occ 109, .occ 114, .occ 161, .occ 166, .occ 246, .occ 248, .occ 250, .occ 283, .occ 285, .occ 287, .occ 288, .occ 294, .occ 297, .occ 302, .occ 314, .occ 317, .occ 364, .occ 365, .occ 395, .occ 480, .occ 482, .occ 488, .occ 501, .occ 508, .occ 525, .occ 526, .occ 534, .occ 538, .occ 542, .occ 607, .occ 701, .sumGe, .nonneg 5, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchLe 22 (0), .branchGe 1 (1), .branchGe 42 (1)]

def plane490GenLeaf0090Mult : Fin 44 → Nat := ![351, 79, 21, 185, 163, 46, 110, 164, 2, 154, 133, 8, 33, 44, 152, 127, 307, 38, 38, 168, 3, 130, 58, 130, 19, 27, 62, 111, 5, 14, 28, 77, 3, 25, 199, 3, 359, 3, 1579, 335, 306, 115, 5, 1268]

theorem plane490GenLeaf0090 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0090Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0090Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0090Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0090Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 93
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 114
  · exact hroot.hOcc 161
  · exact hroot.hOcc 166
  · exact hroot.hOcc 246
  · exact hroot.hOcc 248
  · exact hroot.hOcc 250
  · exact hroot.hOcc 283
  · exact hroot.hOcc 285
  · exact hroot.hOcc 287
  · exact hroot.hOcc 288
  · exact hroot.hOcc 294
  · exact hroot.hOcc 297
  · exact hroot.hOcc 302
  · exact hroot.hOcc 314
  · exact hroot.hOcc 317
  · exact hroot.hOcc 364
  · exact hroot.hOcc 365
  · exact hroot.hOcc 395
  · exact hroot.hOcc 480
  · exact hroot.hOcc 482
  · exact hroot.hOcc 488
  · exact hroot.hOcc 501
  · exact hroot.hOcc 508
  · exact hroot.hOcc 525
  · exact hroot.hOcc 526
  · exact hroot.hOcc 534
  · exact hroot.hOcc 538
  · exact hroot.hOcc 542
  · exact hroot.hOcc 607
  · exact hroot.hOcc 701
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
