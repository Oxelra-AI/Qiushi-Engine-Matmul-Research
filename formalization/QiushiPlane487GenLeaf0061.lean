import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0061Refs : Fin 49 → RowRef 668 48 := ![.occ 99, .occ 106, .occ 118, .occ 165, .occ 169, .occ 201, .occ 211, .occ 225, .occ 234, .occ 237, .occ 260, .occ 275, .occ 280, .occ 315, .occ 351, .occ 363, .occ 379, .occ 381, .occ 386, .occ 387, .occ 389, .occ 390, .occ 401, .occ 437, .occ 440, .occ 513, .occ 515, .occ 526, .occ 537, .occ 580, .occ 584, .occ 595, .occ 614, .occ 637, .occ 647, .occ 650, .occ 653, .occ 657, .occ 661, .sumGe, .nonneg 19, .nonneg 28, .branchGe 39 (1), .branchLe 7 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 36 (0), .branchGe 23 (1), .branchGe 10 (1)]

def plane487GenLeaf0061Mult : Fin 49 → Nat := ![1783, 4966, 54, 2255, 976, 5135, 251, 1551, 931, 11768, 2659, 2947, 6969, 2228, 1490, 7085, 2652, 649, 198, 564, 508, 283, 423, 6265, 1262, 2603, 324, 6205, 84, 85, 367, 85, 883, 1581, 1388, 579, 5947, 4180, 494, 14156, 2239, 200, 28357, 697, 1897, 3549, 11906, 52637, 47074]

theorem plane487GenLeaf0061 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0061Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0061Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0061Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0061Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 99
  · exact hroot.hOcc 106
  · exact hroot.hOcc 118
  · exact hroot.hOcc 165
  · exact hroot.hOcc 169
  · exact hroot.hOcc 201
  · exact hroot.hOcc 211
  · exact hroot.hOcc 225
  · exact hroot.hOcc 234
  · exact hroot.hOcc 237
  · exact hroot.hOcc 260
  · exact hroot.hOcc 275
  · exact hroot.hOcc 280
  · exact hroot.hOcc 315
  · exact hroot.hOcc 351
  · exact hroot.hOcc 363
  · exact hroot.hOcc 379
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 387
  · exact hroot.hOcc 389
  · exact hroot.hOcc 390
  · exact hroot.hOcc 401
  · exact hroot.hOcc 437
  · exact hroot.hOcc 440
  · exact hroot.hOcc 513
  · exact hroot.hOcc 515
  · exact hroot.hOcc 526
  · exact hroot.hOcc 537
  · exact hroot.hOcc 580
  · exact hroot.hOcc 584
  · exact hroot.hOcc 595
  · exact hroot.hOcc 614
  · exact hroot.hOcc 637
  · exact hroot.hOcc 647
  · exact hroot.hOcc 650
  · exact hroot.hOcc 653
  · exact hroot.hOcc 657
  · exact hroot.hOcc 661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (23 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (10 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
