import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0024Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 94, .occ 95, .occ 103, .occ 111, .occ 127, .occ 131, .occ 133, .occ 157, .occ 179, .occ 183, .occ 205, .occ 236, .occ 238, .occ 260, .occ 283, .occ 303, .occ 309, .occ 314, .occ 316, .occ 322, .occ 352, .occ 362, .occ 364, .occ 455, .occ 456, .occ 475, .occ 489, .occ 501, .occ 603, .occ 626, .occ 644, .occ 666, .occ 691, .occ 694, .occ 704, .sumGe, .branchLe 29 (0), .branchLe 23 (0), .branchGe 16 (1), .branchGe 15 (1), .branchGe 32 (1), .branchLe 20 (0), .branchLe 33 (0)]

def plane490GenLeaf0024Mult : Fin 44 → Nat := ![4786, 21635, 5801, 5593, 20156, 14841, 3207, 3407, 13666, 8738, 5415, 12414, 2496, 5574, 3534, 11671, 18071, 1077, 5440, 19935, 4635, 14720, 6637, 6452, 12138, 14167, 4524, 101, 2761, 4973, 3518, 410, 9478, 3565, 476, 3152, 35802, 29476, 31761, 94887, 51949, 89455, 31792, 32284]

theorem plane490GenLeaf0024 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0024Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0024Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0024Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0024Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 103
  · exact hroot.hOcc 111
  · exact hroot.hOcc 127
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 157
  · exact hroot.hOcc 179
  · exact hroot.hOcc 183
  · exact hroot.hOcc 205
  · exact hroot.hOcc 236
  · exact hroot.hOcc 238
  · exact hroot.hOcc 260
  · exact hroot.hOcc 283
  · exact hroot.hOcc 303
  · exact hroot.hOcc 309
  · exact hroot.hOcc 314
  · exact hroot.hOcc 316
  · exact hroot.hOcc 322
  · exact hroot.hOcc 352
  · exact hroot.hOcc 362
  · exact hroot.hOcc 364
  · exact hroot.hOcc 455
  · exact hroot.hOcc 456
  · exact hroot.hOcc 475
  · exact hroot.hOcc 489
  · exact hroot.hOcc 501
  · exact hroot.hOcc 603
  · exact hroot.hOcc 626
  · exact hroot.hOcc 644
  · exact hroot.hOcc 666
  · exact hroot.hOcc 691
  · exact hroot.hOcc 694
  · exact hroot.hOcc 704
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33

end QiushiMatmul
