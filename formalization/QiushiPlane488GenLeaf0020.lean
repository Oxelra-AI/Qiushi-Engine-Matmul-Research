import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0020Refs : Fin 41 → RowRef 413 41 := ![.occ 109, .occ 110, .occ 146, .occ 147, .occ 154, .occ 156, .occ 159, .occ 160, .occ 161, .occ 171, .occ 174, .occ 175, .occ 183, .occ 189, .occ 207, .occ 208, .occ 212, .occ 227, .occ 232, .occ 235, .occ 275, .occ 296, .occ 297, .occ 301, .occ 317, .occ 318, .occ 320, .occ 321, .occ 325, .occ 328, .occ 361, .occ 381, .occ 400, .occ 410, .sumGe, .nonneg 0, .nonneg 7, .branchLe 27 (0), .branchGe 15 (1), .branchLe 14 (0), .branchGe 24 (1)]

def plane488GenLeaf0020Mult : Fin 41 → Nat := ![10557, 10953, 1178, 1742, 1650, 1502, 440, 231, 1667, 1533, 739, 1208, 1880, 4635, 85, 780, 2060, 2023, 4895, 3107, 785, 663, 1121, 2292, 508, 911, 979, 1047, 1818, 1099, 4285, 112, 3305, 3475, 11065, 1864, 2156, 6382, 33793, 6258, 33317]

theorem plane488GenLeaf0020 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0020Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0020Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0020Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0020Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 146
  · exact hroot.hOcc 147
  · exact hroot.hOcc 154
  · exact hroot.hOcc 156
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 161
  · exact hroot.hOcc 171
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 183
  · exact hroot.hOcc 189
  · exact hroot.hOcc 207
  · exact hroot.hOcc 208
  · exact hroot.hOcc 212
  · exact hroot.hOcc 227
  · exact hroot.hOcc 232
  · exact hroot.hOcc 235
  · exact hroot.hOcc 275
  · exact hroot.hOcc 296
  · exact hroot.hOcc 297
  · exact hroot.hOcc 301
  · exact hroot.hOcc 317
  · exact hroot.hOcc 318
  · exact hroot.hOcc 320
  · exact hroot.hOcc 321
  · exact hroot.hOcc 325
  · exact hroot.hOcc 328
  · exact hroot.hOcc 361
  · exact hroot.hOcc 381
  · exact hroot.hOcc 400
  · exact hroot.hOcc 410
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (24 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
