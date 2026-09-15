import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0100Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 95, .occ 97, .occ 105, .occ 106, .occ 108, .occ 114, .occ 138, .occ 144, .occ 160, .occ 165, .occ 167, .occ 215, .occ 250, .occ 271, .occ 291, .occ 295, .occ 303, .occ 311, .occ 325, .occ 340, .occ 349, .occ 362, .occ 400, .occ 403, .occ 448, .occ 453, .occ 494, .occ 533, .occ 542, .occ 556, .occ 562, .occ 602, .occ 632, .occ 670, .occ 671, .sumGe, .nonneg 36, .branchGe 29 (1), .branchGe 18 (1), .branchLe 14 (0), .branchLe 1 (0), .branchGe 21 (1), .branchGe 8 (1)]

def plane490GenLeaf0100Mult : Fin 44 → Nat := ![9, 143, 62, 203, 189, 173, 110, 18, 42, 213, 76, 60, 95, 107, 16, 118, 50, 108, 77, 40, 122, 83, 109, 54, 107, 21, 2, 36, 128, 6, 58, 49, 2, 67, 27, 47, 280, 41, 908, 526, 152, 280, 919, 498]

theorem plane490GenLeaf0100 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0100Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0100Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0100Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0100Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 114
  · exact hroot.hOcc 138
  · exact hroot.hOcc 144
  · exact hroot.hOcc 160
  · exact hroot.hOcc 165
  · exact hroot.hOcc 167
  · exact hroot.hOcc 215
  · exact hroot.hOcc 250
  · exact hroot.hOcc 271
  · exact hroot.hOcc 291
  · exact hroot.hOcc 295
  · exact hroot.hOcc 303
  · exact hroot.hOcc 311
  · exact hroot.hOcc 325
  · exact hroot.hOcc 340
  · exact hroot.hOcc 349
  · exact hroot.hOcc 362
  · exact hroot.hOcc 400
  · exact hroot.hOcc 403
  · exact hroot.hOcc 448
  · exact hroot.hOcc 453
  · exact hroot.hOcc 494
  · exact hroot.hOcc 533
  · exact hroot.hOcc 542
  · exact hroot.hOcc 556
  · exact hroot.hOcc 562
  · exact hroot.hOcc 602
  · exact hroot.hOcc 632
  · exact hroot.hOcc 670
  · exact hroot.hOcc 671
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
