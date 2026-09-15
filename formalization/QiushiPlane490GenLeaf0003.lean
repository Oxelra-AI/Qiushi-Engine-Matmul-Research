import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0003Refs : Fin 44 → RowRef 713 43 := ![.occ 84, .occ 93, .occ 104, .occ 117, .occ 123, .occ 146, .occ 195, .occ 196, .occ 209, .occ 212, .occ 229, .occ 237, .occ 241, .occ 283, .occ 284, .occ 291, .occ 302, .occ 303, .occ 314, .occ 329, .occ 334, .occ 335, .occ 339, .occ 364, .occ 396, .occ 447, .occ 448, .occ 449, .occ 457, .occ 518, .occ 573, .occ 617, .occ 678, .occ 710, .sumGe, .nonneg 24, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchLe 16 (0), .branchLe 39 (0), .branchLe 19 (0), .branchGe 10 (1), .branchLe 27 (0)]

def plane490GenLeaf0003Mult : Fin 44 → Nat := ![142, 283, 938, 625, 1287, 607, 455, 1068, 171, 248, 35, 655, 289, 639, 749, 219, 741, 601, 62, 551, 394, 477, 256, 1596, 343, 443, 256, 357, 369, 676, 63, 846, 318, 763, 3046, 221, 3046, 1013, 1459, 2027, 3046, 2703, 7273, 2283]

theorem plane490GenLeaf0003 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0003Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0003Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 93
  · exact hroot.hOcc 104
  · exact hroot.hOcc 117
  · exact hroot.hOcc 123
  · exact hroot.hOcc 146
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 209
  · exact hroot.hOcc 212
  · exact hroot.hOcc 229
  · exact hroot.hOcc 237
  · exact hroot.hOcc 241
  · exact hroot.hOcc 283
  · exact hroot.hOcc 284
  · exact hroot.hOcc 291
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 314
  · exact hroot.hOcc 329
  · exact hroot.hOcc 334
  · exact hroot.hOcc 335
  · exact hroot.hOcc 339
  · exact hroot.hOcc 364
  · exact hroot.hOcc 396
  · exact hroot.hOcc 447
  · exact hroot.hOcc 448
  · exact hroot.hOcc 449
  · exact hroot.hOcc 457
  · exact hroot.hOcc 518
  · exact hroot.hOcc 573
  · exact hroot.hOcc 617
  · exact hroot.hOcc 678
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27

end QiushiMatmul
