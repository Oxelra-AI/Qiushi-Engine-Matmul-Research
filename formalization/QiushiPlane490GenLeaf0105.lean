import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0105Refs : Fin 43 → RowRef 713 43 := ![.occ 89, .occ 90, .occ 103, .occ 105, .occ 109, .occ 111, .occ 131, .occ 152, .occ 159, .occ 187, .occ 250, .occ 277, .occ 283, .occ 299, .occ 300, .occ 303, .occ 401, .occ 420, .occ 446, .occ 447, .occ 455, .occ 480, .occ 501, .occ 512, .occ 522, .occ 578, .occ 585, .occ 602, .occ 607, .occ 608, .occ 632, .occ 653, .occ 655, .occ 712, .sumGe, .nonneg 19, .branchGe 29 (1), .branchGe 18 (1), .branchLe 14 (0), .branchGe 1 (1), .branchLe 20 (0), .branchGe 15 (1), .branchGe 31 (1)]

def plane490GenLeaf0105Mult : Fin 43 → Nat := ![14, 1, 2, 16, 1, 1, 2, 5, 10, 6, 8, 1, 1, 1, 3, 10, 5, 3, 10, 1, 4, 11, 7, 4, 4, 1, 2, 5, 2, 7, 2, 7, 1, 4, 21, 5, 76, 43, 17, 41, 21, 39, 43]

theorem plane490GenLeaf0105 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0105Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0105Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0105Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0105Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 131
  · exact hroot.hOcc 152
  · exact hroot.hOcc 159
  · exact hroot.hOcc 187
  · exact hroot.hOcc 250
  · exact hroot.hOcc 277
  · exact hroot.hOcc 283
  · exact hroot.hOcc 299
  · exact hroot.hOcc 300
  · exact hroot.hOcc 303
  · exact hroot.hOcc 401
  · exact hroot.hOcc 420
  · exact hroot.hOcc 446
  · exact hroot.hOcc 447
  · exact hroot.hOcc 455
  · exact hroot.hOcc 480
  · exact hroot.hOcc 501
  · exact hroot.hOcc 512
  · exact hroot.hOcc 522
  · exact hroot.hOcc 578
  · exact hroot.hOcc 585
  · exact hroot.hOcc 602
  · exact hroot.hOcc 607
  · exact hroot.hOcc 608
  · exact hroot.hOcc 632
  · exact hroot.hOcc 653
  · exact hroot.hOcc 655
  · exact hroot.hOcc 712
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31

end QiushiMatmul
