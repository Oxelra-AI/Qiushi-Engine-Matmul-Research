import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0111Refs : Fin 44 → RowRef 713 43 := ![.occ 91, .occ 105, .occ 106, .occ 108, .occ 133, .occ 152, .occ 161, .occ 170, .occ 182, .occ 201, .occ 203, .occ 205, .occ 239, .occ 272, .occ 273, .occ 284, .occ 290, .occ 323, .occ 339, .occ 342, .occ 362, .occ 364, .occ 365, .occ 426, .occ 437, .occ 449, .occ 454, .occ 480, .occ 486, .occ 505, .occ 517, .occ 522, .occ 582, .occ 602, .occ 607, .occ 655, .occ 681, .sumGe, .branchGe 29 (1), .branchGe 18 (1), .branchGe 14 (1), .branchLe 32 (0), .branchLe 38 (0), .branchLe 25 (0)]

def plane490GenLeaf0111Mult : Fin 44 → Nat := ![4393, 10150, 632, 11162, 6949, 433, 915, 2211, 1669, 5090, 1318, 2608, 3161, 1211, 1409, 1650, 5138, 914, 2635, 356, 2570, 3617, 574, 462, 2109, 3188, 792, 584, 574, 3389, 2610, 910, 656, 3464, 1566, 451, 561, 11162, 32230, 8821, 33763, 10711, 7189, 11162]

theorem plane490GenLeaf0111 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0111Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0111Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0111Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0111Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 133
  · exact hroot.hOcc 152
  · exact hroot.hOcc 161
  · exact hroot.hOcc 170
  · exact hroot.hOcc 182
  · exact hroot.hOcc 201
  · exact hroot.hOcc 203
  · exact hroot.hOcc 205
  · exact hroot.hOcc 239
  · exact hroot.hOcc 272
  · exact hroot.hOcc 273
  · exact hroot.hOcc 284
  · exact hroot.hOcc 290
  · exact hroot.hOcc 323
  · exact hroot.hOcc 339
  · exact hroot.hOcc 342
  · exact hroot.hOcc 362
  · exact hroot.hOcc 364
  · exact hroot.hOcc 365
  · exact hroot.hOcc 426
  · exact hroot.hOcc 437
  · exact hroot.hOcc 449
  · exact hroot.hOcc 454
  · exact hroot.hOcc 480
  · exact hroot.hOcc 486
  · exact hroot.hOcc 505
  · exact hroot.hOcc 517
  · exact hroot.hOcc 522
  · exact hroot.hOcc 582
  · exact hroot.hOcc 602
  · exact hroot.hOcc 607
  · exact hroot.hOcc 655
  · exact hroot.hOcc 681
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25

end QiushiMatmul
