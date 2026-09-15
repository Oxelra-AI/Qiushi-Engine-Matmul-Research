import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0071Refs : Fin 39 → RowRef 713 43 := ![.occ 85, .occ 94, .occ 102, .occ 104, .occ 114, .occ 115, .occ 116, .occ 119, .occ 158, .occ 202, .occ 226, .occ 228, .occ 239, .occ 256, .occ 257, .occ 274, .occ 283, .occ 291, .occ 295, .occ 331, .occ 343, .occ 434, .occ 448, .occ 461, .occ 466, .occ 480, .occ 494, .occ 542, .occ 572, .occ 577, .occ 652, .sumGe, .nonneg 30, .branchLe 29 (0), .branchGe 4 (1), .branchGe 34 (1), .branchLe 3 (0), .branchLe 40 (0), .branchLe 14 (0)]

def plane490GenLeaf0071Mult : Fin 39 → Nat := ![2, 2, 5, 5, 11, 1, 3, 8, 8, 7, 6, 1, 1, 1, 9, 14, 6, 1, 5, 2, 9, 3, 7, 2, 1, 1, 1, 3, 2, 2, 4, 17, 1, 17, 51, 44, 16, 16, 17]

theorem plane490GenLeaf0071 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0071Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0071Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0071Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0071Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 94
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 158
  · exact hroot.hOcc 202
  · exact hroot.hOcc 226
  · exact hroot.hOcc 228
  · exact hroot.hOcc 239
  · exact hroot.hOcc 256
  · exact hroot.hOcc 257
  · exact hroot.hOcc 274
  · exact hroot.hOcc 283
  · exact hroot.hOcc 291
  · exact hroot.hOcc 295
  · exact hroot.hOcc 331
  · exact hroot.hOcc 343
  · exact hroot.hOcc 434
  · exact hroot.hOcc 448
  · exact hroot.hOcc 461
  · exact hroot.hOcc 466
  · exact hroot.hOcc 480
  · exact hroot.hOcc 494
  · exact hroot.hOcc 542
  · exact hroot.hOcc 572
  · exact hroot.hOcc 577
  · exact hroot.hOcc 652
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
