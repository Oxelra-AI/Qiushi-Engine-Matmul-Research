import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0013Refs : Fin 42 → RowRef 413 41 := ![.occ 88, .occ 102, .occ 115, .occ 116, .occ 118, .occ 139, .occ 144, .occ 156, .occ 159, .occ 171, .occ 172, .occ 174, .occ 175, .occ 177, .occ 186, .occ 187, .occ 190, .occ 192, .occ 203, .occ 210, .occ 215, .occ 216, .occ 219, .occ 241, .occ 248, .occ 259, .occ 268, .occ 298, .occ 308, .occ 363, .occ 374, .occ 390, .occ 408, .sumGe, .nonneg 0, .branchLe 27 (0), .branchLe 15 (0), .branchLe 20 (0), .branchGe 25 (1), .branchGe 1 (1), .branchGe 6 (1), .branchLe 21 (0)]

def plane488GenLeaf0013Mult : Fin 42 → Nat := ![964, 747, 492, 907, 173, 553, 1097, 49, 406, 212, 163, 286, 104, 768, 420, 151, 165, 462, 407, 62, 151, 173, 57, 320, 411, 594, 1096, 444, 63, 420, 358, 294, 33, 1516, 838, 1322, 705, 1167, 3097, 2679, 5145, 838]

theorem plane488GenLeaf0013 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0013Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0013Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 88
  · exact hroot.hOcc 102
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 139
  · exact hroot.hOcc 144
  · exact hroot.hOcc 156
  · exact hroot.hOcc 159
  · exact hroot.hOcc 171
  · exact hroot.hOcc 172
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 177
  · exact hroot.hOcc 186
  · exact hroot.hOcc 187
  · exact hroot.hOcc 190
  · exact hroot.hOcc 192
  · exact hroot.hOcc 203
  · exact hroot.hOcc 210
  · exact hroot.hOcc 215
  · exact hroot.hOcc 216
  · exact hroot.hOcc 219
  · exact hroot.hOcc 241
  · exact hroot.hOcc 248
  · exact hroot.hOcc 259
  · exact hroot.hOcc 268
  · exact hroot.hOcc 298
  · exact hroot.hOcc 308
  · exact hroot.hOcc 363
  · exact hroot.hOcc 374
  · exact hroot.hOcc 390
  · exact hroot.hOcc 408
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (25 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (1 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (6 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21

end QiushiMatmul
