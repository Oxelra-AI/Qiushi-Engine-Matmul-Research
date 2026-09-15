import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0080Refs : Fin 44 → RowRef 713 43 := ![.occ 84, .occ 85, .occ 86, .occ 89, .occ 90, .occ 102, .occ 105, .occ 107, .occ 108, .occ 116, .occ 156, .occ 161, .occ 168, .occ 171, .occ 178, .occ 202, .occ 248, .occ 250, .occ 290, .occ 299, .occ 334, .occ 364, .occ 375, .occ 471, .occ 486, .occ 505, .occ 520, .occ 565, .occ 607, .occ 624, .occ 653, .occ 664, .occ 670, .occ 709, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchLe 22 (0), .branchLe 42 (0), .branchLe 32 (0), .branchLe 8 (0), .branchLe 16 (0), .branchLe 2 (0)]

def plane490GenLeaf0080Mult : Fin 44 → Nat := ![105, 282, 70, 335, 223, 252, 743, 282, 155, 30, 77, 275, 182, 244, 459, 390, 47, 430, 209, 99, 121, 166, 32, 101, 232, 131, 50, 42, 67, 9, 360, 23, 50, 131, 840, 2209, 840, 610, 840, 607, 840, 840, 709, 840]

theorem plane490GenLeaf0080 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0080Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0080Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0080Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0080Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 116
  · exact hroot.hOcc 156
  · exact hroot.hOcc 161
  · exact hroot.hOcc 168
  · exact hroot.hOcc 171
  · exact hroot.hOcc 178
  · exact hroot.hOcc 202
  · exact hroot.hOcc 248
  · exact hroot.hOcc 250
  · exact hroot.hOcc 290
  · exact hroot.hOcc 299
  · exact hroot.hOcc 334
  · exact hroot.hOcc 364
  · exact hroot.hOcc 375
  · exact hroot.hOcc 471
  · exact hroot.hOcc 486
  · exact hroot.hOcc 505
  · exact hroot.hOcc 520
  · exact hroot.hOcc 565
  · exact hroot.hOcc 607
  · exact hroot.hOcc 624
  · exact hroot.hOcc 653
  · exact hroot.hOcc 664
  · exact hroot.hOcc 670
  · exact hroot.hOcc 709
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2

end QiushiMatmul
