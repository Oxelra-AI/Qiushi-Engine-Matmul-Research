import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0060Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 90, .occ 94, .occ 109, .occ 110, .occ 119, .occ 175, .occ 186, .occ 189, .occ 196, .occ 202, .occ 204, .occ 239, .occ 244, .occ 252, .occ 268, .occ 274, .occ 290, .occ 295, .occ 314, .occ 335, .occ 375, .occ 395, .occ 427, .occ 463, .occ 464, .occ 466, .occ 542, .occ 576, .occ 599, .occ 603, .occ 632, .occ 673, .occ 688, .occ 697, .sumGe, .nonneg 41, .branchLe 29 (0), .branchGe 4 (1), .branchLe 34 (0), .branchLe 23 (0), .branchGe 39 (1), .branchLe 18 (0), .branchLe 15 (0)]

def plane490GenLeaf0060Mult : Fin 44 → Nat := ![153, 4750, 12190, 8672, 1039, 10494, 3626, 1119, 7746, 4989, 16331, 3811, 1862, 5084, 7358, 5321, 12589, 9720, 7643, 4909, 1780, 5348, 3859, 1119, 5545, 7308, 4192, 635, 3048, 1997, 3218, 1336, 1876, 3410, 2821, 26668, 2141, 19101, 79672, 5113, 26033, 26105, 23847, 24697]

theorem plane490GenLeaf0060 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0060Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0060Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0060Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0060Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 94
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 119
  · exact hroot.hOcc 175
  · exact hroot.hOcc 186
  · exact hroot.hOcc 189
  · exact hroot.hOcc 196
  · exact hroot.hOcc 202
  · exact hroot.hOcc 204
  · exact hroot.hOcc 239
  · exact hroot.hOcc 244
  · exact hroot.hOcc 252
  · exact hroot.hOcc 268
  · exact hroot.hOcc 274
  · exact hroot.hOcc 290
  · exact hroot.hOcc 295
  · exact hroot.hOcc 314
  · exact hroot.hOcc 335
  · exact hroot.hOcc 375
  · exact hroot.hOcc 395
  · exact hroot.hOcc 427
  · exact hroot.hOcc 463
  · exact hroot.hOcc 464
  · exact hroot.hOcc 466
  · exact hroot.hOcc 542
  · exact hroot.hOcc 576
  · exact hroot.hOcc 599
  · exact hroot.hOcc 603
  · exact hroot.hOcc 632
  · exact hroot.hOcc 673
  · exact hroot.hOcc 688
  · exact hroot.hOcc 697
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15

end QiushiMatmul
