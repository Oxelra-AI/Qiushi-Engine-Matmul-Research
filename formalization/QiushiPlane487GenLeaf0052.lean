import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0052Refs : Fin 49 → RowRef 668 48 := ![.occ 82, .occ 85, .occ 94, .occ 103, .occ 121, .occ 160, .occ 165, .occ 188, .occ 209, .occ 217, .occ 225, .occ 260, .occ 294, .occ 303, .occ 308, .occ 347, .occ 356, .occ 390, .occ 391, .occ 401, .occ 405, .occ 408, .occ 414, .occ 472, .occ 523, .occ 526, .occ 544, .occ 595, .occ 603, .occ 604, .occ 608, .occ 644, .occ 650, .occ 652, .occ 657, .occ 665, .sumGe, .nonneg 0, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 19 (0), .branchLe 36 (0), .branchLe 23 (0), .branchLe 45 (0), .branchGe 5 (1), .branchLe 1 (0)]

def plane487GenLeaf0052Mult : Fin 49 → Nat := ![2411, 3214, 872, 1778, 8360, 3598, 1840, 5113, 8446, 10424, 5693, 13705, 964, 1664, 1352, 7531, 4577, 3777, 6410, 5715, 6696, 11479, 9583, 13169, 3787, 2711, 6929, 2525, 125, 1776, 908, 2103, 6355, 508, 6567, 3822, 32980, 10366, 49743, 9483, 22229, 13570, 30877, 22083, 19324, 21091, 22451, 64823, 32980]

theorem plane487GenLeaf0052 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_45 : x 45 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0052Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0052Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0052Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0052Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 85
  · exact hroot.hOcc 94
  · exact hroot.hOcc 103
  · exact hroot.hOcc 121
  · exact hroot.hOcc 160
  · exact hroot.hOcc 165
  · exact hroot.hOcc 188
  · exact hroot.hOcc 209
  · exact hroot.hOcc 217
  · exact hroot.hOcc 225
  · exact hroot.hOcc 260
  · exact hroot.hOcc 294
  · exact hroot.hOcc 303
  · exact hroot.hOcc 308
  · exact hroot.hOcc 347
  · exact hroot.hOcc 356
  · exact hroot.hOcc 390
  · exact hroot.hOcc 391
  · exact hroot.hOcc 401
  · exact hroot.hOcc 405
  · exact hroot.hOcc 408
  · exact hroot.hOcc 414
  · exact hroot.hOcc 472
  · exact hroot.hOcc 523
  · exact hroot.hOcc 526
  · exact hroot.hOcc 544
  · exact hroot.hOcc 595
  · exact hroot.hOcc 603
  · exact hroot.hOcc 604
  · exact hroot.hOcc 608
  · exact hroot.hOcc 644
  · exact hroot.hOcc 650
  · exact hroot.hOcc 652
  · exact hroot.hOcc 657
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (45 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45
  · change (∑ k, (if k = (5 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (1 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1

end QiushiMatmul
