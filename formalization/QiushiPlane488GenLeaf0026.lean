import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0026Refs : Fin 42 → RowRef 413 41 := ![.occ 86, .occ 90, .occ 94, .occ 105, .occ 108, .occ 134, .occ 135, .occ 143, .occ 148, .occ 149, .occ 175, .occ 178, .occ 189, .occ 190, .occ 195, .occ 196, .occ 231, .occ 254, .occ 260, .occ 265, .occ 272, .occ 278, .occ 300, .occ 310, .occ 324, .occ 333, .occ 342, .occ 357, .occ 372, .occ 386, .occ 395, .occ 396, .occ 397, .sumGe, .nonneg 8, .nonneg 20, .branchGe 27 (1), .branchLe 19 (0), .branchLe 16 (0), .branchLe 22 (0), .branchGe 40 (1), .branchGe 35 (1)]

def plane488GenLeaf0026Mult : Fin 42 → Nat := ![938, 491, 684, 1325, 372, 10, 788, 238, 236, 753, 535, 448, 337, 338, 391, 1352, 45, 265, 345, 410, 179, 304, 189, 126, 329, 64, 258, 551, 15, 225, 523, 175, 35, 1716, 113, 219, 4668, 955, 1401, 1021, 2114, 2210]

theorem plane488GenLeaf0026 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0026Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0026Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0026Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0026Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 90
  · exact hroot.hOcc 94
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 143
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 175
  · exact hroot.hOcc 178
  · exact hroot.hOcc 189
  · exact hroot.hOcc 190
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 231
  · exact hroot.hOcc 254
  · exact hroot.hOcc 260
  · exact hroot.hOcc 265
  · exact hroot.hOcc 272
  · exact hroot.hOcc 278
  · exact hroot.hOcc 300
  · exact hroot.hOcc 310
  · exact hroot.hOcc 324
  · exact hroot.hOcc 333
  · exact hroot.hOcc 342
  · exact hroot.hOcc 357
  · exact hroot.hOcc 372
  · exact hroot.hOcc 386
  · exact hroot.hOcc 395
  · exact hroot.hOcc 396
  · exact hroot.hOcc 397
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (20 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (27 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (16 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (40 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (35 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
