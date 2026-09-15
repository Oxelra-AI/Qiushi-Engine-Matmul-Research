import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0110Refs : Fin 44 → RowRef 713 43 := ![.occ 94, .occ 95, .occ 104, .occ 106, .occ 108, .occ 132, .occ 141, .occ 159, .occ 160, .occ 246, .occ 258, .occ 262, .occ 263, .occ 391, .occ 410, .occ 424, .occ 431, .occ 446, .occ 450, .occ 484, .occ 494, .occ 500, .occ 517, .occ 521, .occ 542, .occ 550, .occ 562, .occ 593, .occ 602, .occ 632, .occ 649, .occ 671, .sumGe, .nonneg 11, .nonneg 22, .nonneg 24, .branchGe 29 (1), .branchGe 18 (1), .branchLe 14 (0), .branchGe 1 (1), .branchGe 20 (1), .branchGe 8 (1), .branchGe 0 (1), .branchGe 16 (1)]

def plane490GenLeaf0110Mult : Fin 44 → Nat := ![72, 362, 349, 451, 604, 106, 24, 215, 331, 95, 36, 69, 255, 102, 141, 197, 118, 56, 23, 112, 407, 33, 107, 132, 35, 17, 305, 118, 242, 217, 86, 22, 604, 21, 20, 21, 2067, 1335, 148, 138, 1752, 721, 394, 1001]

theorem plane490GenLeaf0110 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0110Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0110Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0110Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0110Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 132
  · exact hroot.hOcc 141
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 246
  · exact hroot.hOcc 258
  · exact hroot.hOcc 262
  · exact hroot.hOcc 263
  · exact hroot.hOcc 391
  · exact hroot.hOcc 410
  · exact hroot.hOcc 424
  · exact hroot.hOcc 431
  · exact hroot.hOcc 446
  · exact hroot.hOcc 450
  · exact hroot.hOcc 484
  · exact hroot.hOcc 494
  · exact hroot.hOcc 500
  · exact hroot.hOcc 517
  · exact hroot.hOcc 521
  · exact hroot.hOcc 542
  · exact hroot.hOcc 550
  · exact hroot.hOcc 562
  · exact hroot.hOcc 593
  · exact hroot.hOcc 602
  · exact hroot.hOcc 632
  · exact hroot.hOcc 649
  · exact hroot.hOcc 671
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
