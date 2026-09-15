import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0050Refs : Fin 49 → RowRef 668 48 := ![.occ 85, .occ 89, .occ 106, .occ 118, .occ 246, .occ 260, .occ 281, .occ 286, .occ 303, .occ 309, .occ 315, .occ 334, .occ 343, .occ 347, .occ 372, .occ 375, .occ 386, .occ 401, .occ 457, .occ 469, .occ 504, .occ 505, .occ 529, .occ 550, .occ 583, .occ 587, .occ 592, .occ 608, .occ 622, .occ 645, .occ 650, .occ 656, .occ 660, .occ 661, .occ 666, .sumGe, .nonneg 7, .nonneg 31, .branchGe 39 (1), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 19 (0), .branchLe 36 (0), .branchLe 23 (0), .branchLe 45 (0), .branchLe 5 (0), .branchLe 25 (0), .branchGe 30 (1)]

def plane487GenLeaf0050Mult : Fin 49 → Nat := ![38352, 10712, 53388, 4876, 40555, 7120, 17852, 20196, 41799, 5030, 43109, 2724, 38604, 17212, 9010, 17724, 1354, 10298, 52128, 13716, 3708, 5898, 2350, 11874, 8566, 7814, 17008, 14280, 4394, 9763, 18112, 17910, 3929, 39486, 9280, 125285, 123926, 6430, 114766, 71236, 68420, 115522, 73928, 20872, 56854, 102956, 97612, 48846, 270564]

theorem plane487GenLeaf0050 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_45 : x 45 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0050Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0050Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0050Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0050Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 89
  · exact hroot.hOcc 106
  · exact hroot.hOcc 118
  · exact hroot.hOcc 246
  · exact hroot.hOcc 260
  · exact hroot.hOcc 281
  · exact hroot.hOcc 286
  · exact hroot.hOcc 303
  · exact hroot.hOcc 309
  · exact hroot.hOcc 315
  · exact hroot.hOcc 334
  · exact hroot.hOcc 343
  · exact hroot.hOcc 347
  · exact hroot.hOcc 372
  · exact hroot.hOcc 375
  · exact hroot.hOcc 386
  · exact hroot.hOcc 401
  · exact hroot.hOcc 457
  · exact hroot.hOcc 469
  · exact hroot.hOcc 504
  · exact hroot.hOcc 505
  · exact hroot.hOcc 529
  · exact hroot.hOcc 550
  · exact hroot.hOcc 583
  · exact hroot.hOcc 587
  · exact hroot.hOcc 592
  · exact hroot.hOcc 608
  · exact hroot.hOcc 622
  · exact hroot.hOcc 645
  · exact hroot.hOcc 650
  · exact hroot.hOcc 656
  · exact hroot.hOcc 660
  · exact hroot.hOcc 661
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (31 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (45 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45
  · change (∑ k, (if k = (5 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (30 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30

end QiushiMatmul
