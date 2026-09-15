import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0050Refs : Fin 43 → RowRef 713 43 := ![.occ 89, .occ 91, .occ 103, .occ 106, .occ 114, .occ 116, .occ 164, .occ 165, .occ 201, .occ 219, .occ 236, .occ 237, .occ 271, .occ 284, .occ 302, .occ 303, .occ 335, .occ 362, .occ 364, .occ 449, .occ 451, .occ 453, .occ 460, .occ 480, .occ 549, .occ 551, .occ 563, .occ 617, .occ 626, .occ 627, .occ 668, .occ 679, .occ 703, .occ 706, .sumGe, .nonneg 35, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchGe 28 (1), .branchLe 39 (0), .branchGe 21 (1)]

def plane490GenLeaf0050Mult : Fin 43 → Nat := ![51, 176, 40, 24, 376, 248, 24, 181, 193, 102, 323, 359, 176, 89, 2, 127, 265, 110, 142, 130, 10, 100, 86, 147, 5, 41, 6, 56, 17, 14, 66, 21, 25, 16, 516, 324, 516, 490, 24, 374, 1238, 430, 1346]

theorem plane490GenLeaf0050 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0050Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0050Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0050Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0050Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 201
  · exact hroot.hOcc 219
  · exact hroot.hOcc 236
  · exact hroot.hOcc 237
  · exact hroot.hOcc 271
  · exact hroot.hOcc 284
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 335
  · exact hroot.hOcc 362
  · exact hroot.hOcc 364
  · exact hroot.hOcc 449
  · exact hroot.hOcc 451
  · exact hroot.hOcc 453
  · exact hroot.hOcc 460
  · exact hroot.hOcc 480
  · exact hroot.hOcc 549
  · exact hroot.hOcc 551
  · exact hroot.hOcc 563
  · exact hroot.hOcc 617
  · exact hroot.hOcc 626
  · exact hroot.hOcc 627
  · exact hroot.hOcc 668
  · exact hroot.hOcc 679
  · exact hroot.hOcc 703
  · exact hroot.hOcc 706
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
