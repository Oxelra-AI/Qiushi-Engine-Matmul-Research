import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0086Refs : Fin 44 → RowRef 713 43 := ![.occ 84, .occ 91, .occ 94, .occ 105, .occ 106, .occ 108, .occ 111, .occ 115, .occ 149, .occ 150, .occ 201, .occ 202, .occ 250, .occ 274, .occ 298, .occ 302, .occ 303, .occ 316, .occ 366, .occ 375, .occ 472, .occ 500, .occ 505, .occ 513, .occ 564, .occ 632, .occ 645, .occ 649, .occ 653, .occ 655, .occ 671, .occ 691, .occ 694, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchLe 22 (0), .branchGe 1 (1), .branchLe 42 (0), .branchGe 32 (1), .branchLe 2 (0), .branchLe 34 (0), .branchLe 37 (0)]

def plane490GenLeaf0086Mult : Fin 44 → Nat := ![114, 184, 238, 352, 151, 398, 111, 224, 258, 34, 91, 87, 9, 137, 11, 148, 50, 178, 53, 137, 96, 4, 128, 82, 31, 177, 156, 41, 87, 124, 188, 83, 8, 572, 1163, 357, 253, 395, 72, 331, 1168, 564, 481, 444]

theorem plane490GenLeaf0086 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0086Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0086Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0086Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0086Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 115
  · exact hroot.hOcc 149
  · exact hroot.hOcc 150
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 250
  · exact hroot.hOcc 274
  · exact hroot.hOcc 298
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 316
  · exact hroot.hOcc 366
  · exact hroot.hOcc 375
  · exact hroot.hOcc 472
  · exact hroot.hOcc 500
  · exact hroot.hOcc 505
  · exact hroot.hOcc 513
  · exact hroot.hOcc 564
  · exact hroot.hOcc 632
  · exact hroot.hOcc 645
  · exact hroot.hOcc 649
  · exact hroot.hOcc 653
  · exact hroot.hOcc 655
  · exact hroot.hOcc 671
  · exact hroot.hOcc 691
  · exact hroot.hOcc 694
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37

end QiushiMatmul
