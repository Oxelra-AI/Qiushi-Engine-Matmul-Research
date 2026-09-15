import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0016Refs : Fin 41 → RowRef 413 41 := ![.occ 96, .occ 98, .occ 103, .occ 107, .occ 122, .occ 124, .occ 129, .occ 137, .occ 154, .occ 158, .occ 159, .occ 170, .occ 182, .occ 186, .occ 187, .occ 188, .occ 190, .occ 194, .occ 225, .occ 228, .occ 229, .occ 232, .occ 239, .occ 259, .occ 264, .occ 265, .occ 284, .occ 329, .occ 332, .occ 343, .occ 366, .occ 381, .occ 399, .occ 403, .sumGe, .nonneg 7, .branchLe 27 (0), .branchLe 15 (0), .branchGe 20 (1), .branchLe 39 (0), .branchGe 31 (1)]

def plane488GenLeaf0016Mult : Fin 41 → Nat := ![476, 474, 306, 1168, 1203, 599, 302, 832, 234, 156, 466, 643, 35, 727, 813, 163, 169, 250, 780, 405, 679, 307, 84, 229, 834, 191, 311, 19, 272, 606, 99, 334, 406, 661, 2136, 191, 2117, 2136, 6272, 2136, 4589]

theorem plane488GenLeaf0016 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0016Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0016Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0016Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0016Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 96
  · exact hroot.hOcc 98
  · exact hroot.hOcc 103
  · exact hroot.hOcc 107
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 137
  · exact hroot.hOcc 154
  · exact hroot.hOcc 158
  · exact hroot.hOcc 159
  · exact hroot.hOcc 170
  · exact hroot.hOcc 182
  · exact hroot.hOcc 186
  · exact hroot.hOcc 187
  · exact hroot.hOcc 188
  · exact hroot.hOcc 190
  · exact hroot.hOcc 194
  · exact hroot.hOcc 225
  · exact hroot.hOcc 228
  · exact hroot.hOcc 229
  · exact hroot.hOcc 232
  · exact hroot.hOcc 239
  · exact hroot.hOcc 259
  · exact hroot.hOcc 264
  · exact hroot.hOcc 265
  · exact hroot.hOcc 284
  · exact hroot.hOcc 329
  · exact hroot.hOcc 332
  · exact hroot.hOcc 343
  · exact hroot.hOcc 366
  · exact hroot.hOcc 381
  · exact hroot.hOcc 399
  · exact hroot.hOcc 403
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (39 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (31 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31

end QiushiMatmul
