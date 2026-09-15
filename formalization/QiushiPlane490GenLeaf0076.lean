import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0076Refs : Fin 44 → RowRef 713 43 := ![.occ 91, .occ 93, .occ 105, .occ 106, .occ 108, .occ 112, .occ 152, .occ 161, .occ 168, .occ 246, .occ 250, .occ 274, .occ 284, .occ 290, .occ 294, .occ 311, .occ 314, .occ 335, .occ 354, .occ 375, .occ 486, .occ 521, .occ 526, .occ 540, .occ 542, .occ 595, .occ 602, .occ 603, .occ 626, .occ 632, .occ 636, .occ 670, .occ 673, .occ 704, .occ 705, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchLe 22 (0), .branchLe 1 (0), .branchLe 10 (0), .branchLe 14 (0), .branchLe 9 (0)]

def plane490GenLeaf0076Mult : Fin 44 → Nat := ![14398, 26561, 53885, 5935, 31933, 21123, 10095, 16790, 6571, 16314, 18725, 3124, 14908, 1166, 22247, 9950, 1718, 94, 13826, 2031, 4826, 5413, 2148, 1365, 16837, 12610, 2590, 11894, 8207, 17004, 14665, 7340, 5283, 12483, 694, 63835, 169080, 61245, 21793, 31923, 63835, 47139, 60257, 63835]

theorem plane490GenLeaf0076 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0076Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0076Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0076Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0076Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 93
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 112
  · exact hroot.hOcc 152
  · exact hroot.hOcc 161
  · exact hroot.hOcc 168
  · exact hroot.hOcc 246
  · exact hroot.hOcc 250
  · exact hroot.hOcc 274
  · exact hroot.hOcc 284
  · exact hroot.hOcc 290
  · exact hroot.hOcc 294
  · exact hroot.hOcc 311
  · exact hroot.hOcc 314
  · exact hroot.hOcc 335
  · exact hroot.hOcc 354
  · exact hroot.hOcc 375
  · exact hroot.hOcc 486
  · exact hroot.hOcc 521
  · exact hroot.hOcc 526
  · exact hroot.hOcc 540
  · exact hroot.hOcc 542
  · exact hroot.hOcc 595
  · exact hroot.hOcc 602
  · exact hroot.hOcc 603
  · exact hroot.hOcc 626
  · exact hroot.hOcc 632
  · exact hroot.hOcc 636
  · exact hroot.hOcc 670
  · exact hroot.hOcc 673
  · exact hroot.hOcc 704
  · exact hroot.hOcc 705
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
