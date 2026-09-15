import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0089Refs : Fin 44 → RowRef 713 43 := ![.occ 93, .occ 95, .occ 105, .occ 108, .occ 111, .occ 112, .occ 120, .occ 171, .occ 172, .occ 203, .occ 216, .occ 219, .occ 228, .occ 245, .occ 246, .occ 250, .occ 273, .occ 274, .occ 290, .occ 302, .occ 303, .occ 364, .occ 462, .occ 472, .occ 505, .occ 538, .occ 602, .occ 603, .occ 612, .occ 632, .occ 636, .occ 641, .occ 655, .occ 671, .occ 694, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchLe 22 (0), .branchGe 1 (1), .branchLe 42 (0), .branchGe 32 (1), .branchGe 2 (1)]

def plane490GenLeaf0089Mult : Fin 44 → Nat := ![265, 722, 616, 481, 245, 169, 525, 59, 81, 243, 91, 86, 180, 36, 8, 81, 45, 131, 185, 155, 187, 72, 164, 86, 157, 202, 58, 328, 39, 202, 22, 204, 100, 85, 153, 802, 1341, 491, 484, 600, 422, 645, 1654, 2150]

theorem plane490GenLeaf0089 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0089Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0089Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0089Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0089Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 120
  · exact hroot.hOcc 171
  · exact hroot.hOcc 172
  · exact hroot.hOcc 203
  · exact hroot.hOcc 216
  · exact hroot.hOcc 219
  · exact hroot.hOcc 228
  · exact hroot.hOcc 245
  · exact hroot.hOcc 246
  · exact hroot.hOcc 250
  · exact hroot.hOcc 273
  · exact hroot.hOcc 274
  · exact hroot.hOcc 290
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 364
  · exact hroot.hOcc 462
  · exact hroot.hOcc 472
  · exact hroot.hOcc 505
  · exact hroot.hOcc 538
  · exact hroot.hOcc 602
  · exact hroot.hOcc 603
  · exact hroot.hOcc 612
  · exact hroot.hOcc 632
  · exact hroot.hOcc 636
  · exact hroot.hOcc 641
  · exact hroot.hOcc 655
  · exact hroot.hOcc 671
  · exact hroot.hOcc 694
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
