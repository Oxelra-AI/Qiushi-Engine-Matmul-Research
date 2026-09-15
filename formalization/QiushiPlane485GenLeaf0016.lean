import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0016Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 110, .occ 120, .occ 127, .occ 132, .occ 134, .occ 136, .occ 149, .occ 154, .occ 168, .occ 179, .occ 181, .occ 184, .occ 210, .occ 213, .occ 222, .occ 232, .occ 252, .occ 257, .occ 262, .occ 265, .occ 277, .occ 279, .occ 297, .occ 312, .occ 336, .occ 337, .occ 346, .occ 358, .occ 362, .occ 366, .occ 372, .occ 408, .sumGe, .nonneg 12, .branchLe 28 (0), .branchLe 21 (0), .branchGe 14 (1), .branchLe 29 (0), .branchLe 13 (0), .branchLe 15 (0), .branchGe 31 (1)]

def plane485GenLeaf0016Mult : Fin 42 → Nat := ![26154, 12072, 4191, 4316, 4200, 1651, 15118, 7426, 8370, 2932, 7064, 11971, 16538, 566, 3826, 13775, 12405, 23964, 9997, 2932, 2561, 1008, 2673, 2817, 4929, 2035, 1664, 2048, 5426, 2035, 4030, 5339, 882, 32386, 1008, 29713, 10068, 56810, 30338, 15848, 5072, 80638]

theorem plane485GenLeaf0016 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0016Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0016Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0016Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0016Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 110
  · exact hroot.hOcc 120
  · exact hroot.hOcc 127
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 149
  · exact hroot.hOcc 154
  · exact hroot.hOcc 168
  · exact hroot.hOcc 179
  · exact hroot.hOcc 181
  · exact hroot.hOcc 184
  · exact hroot.hOcc 210
  · exact hroot.hOcc 213
  · exact hroot.hOcc 222
  · exact hroot.hOcc 232
  · exact hroot.hOcc 252
  · exact hroot.hOcc 257
  · exact hroot.hOcc 262
  · exact hroot.hOcc 265
  · exact hroot.hOcc 277
  · exact hroot.hOcc 279
  · exact hroot.hOcc 297
  · exact hroot.hOcc 312
  · exact hroot.hOcc 336
  · exact hroot.hOcc 337
  · exact hroot.hOcc 346
  · exact hroot.hOcc 358
  · exact hroot.hOcc 362
  · exact hroot.hOcc 366
  · exact hroot.hOcc 372
  · exact hroot.hOcc 408
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (12 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (29 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (13 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (31 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31

end QiushiMatmul
