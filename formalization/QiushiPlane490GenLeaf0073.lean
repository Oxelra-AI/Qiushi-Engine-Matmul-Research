import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0073Refs : Fin 41 → RowRef 713 43 := ![.occ 94, .occ 102, .occ 104, .occ 109, .occ 112, .occ 114, .occ 115, .occ 128, .occ 156, .occ 158, .occ 174, .occ 175, .occ 195, .occ 204, .occ 228, .occ 229, .occ 257, .occ 260, .occ 274, .occ 295, .occ 312, .occ 336, .occ 362, .occ 379, .occ 390, .occ 404, .occ 409, .occ 448, .occ 467, .occ 489, .occ 493, .occ 533, .occ 542, .occ 700, .occ 709, .sumGe, .branchLe 29 (0), .branchGe 4 (1), .branchGe 34 (1), .branchLe 3 (0), .branchGe 40 (1)]

def plane490GenLeaf0073Mult : Fin 41 → Nat := ![1, 8, 1, 5, 6, 16, 13, 5, 4, 13, 2, 16, 7, 6, 1, 4, 11, 6, 8, 3, 5, 4, 8, 1, 3, 1, 3, 1, 5, 2, 5, 1, 4, 4, 4, 20, 16, 72, 53, 15, 44]

theorem plane490GenLeaf0073 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0073Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0073Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0073Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0073Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 128
  · exact hroot.hOcc 156
  · exact hroot.hOcc 158
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 195
  · exact hroot.hOcc 204
  · exact hroot.hOcc 228
  · exact hroot.hOcc 229
  · exact hroot.hOcc 257
  · exact hroot.hOcc 260
  · exact hroot.hOcc 274
  · exact hroot.hOcc 295
  · exact hroot.hOcc 312
  · exact hroot.hOcc 336
  · exact hroot.hOcc 362
  · exact hroot.hOcc 379
  · exact hroot.hOcc 390
  · exact hroot.hOcc 404
  · exact hroot.hOcc 409
  · exact hroot.hOcc 448
  · exact hroot.hOcc 467
  · exact hroot.hOcc 489
  · exact hroot.hOcc 493
  · exact hroot.hOcc 533
  · exact hroot.hOcc 542
  · exact hroot.hOcc 700
  · exact hroot.hOcc 709
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
