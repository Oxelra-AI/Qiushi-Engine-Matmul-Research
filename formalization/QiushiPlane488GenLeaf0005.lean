import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0005Refs : Fin 42 → RowRef 413 41 := ![.occ 87, .occ 93, .occ 95, .occ 101, .occ 109, .occ 142, .occ 156, .occ 159, .occ 169, .occ 175, .occ 184, .occ 186, .occ 188, .occ 190, .occ 192, .occ 198, .occ 199, .occ 202, .occ 210, .occ 212, .occ 220, .occ 225, .occ 232, .occ 259, .occ 278, .occ 286, .occ 290, .occ 315, .occ 349, .occ 361, .occ 381, .occ 395, .occ 402, .sumGe, .nonneg 8, .branchLe 27 (0), .branchLe 15 (0), .branchLe 20 (0), .branchLe 25 (0), .branchLe 13 (0), .branchGe 24 (1), .branchLe 23 (0)]

def plane488GenLeaf0005Mult : Fin 42 → Nat := ![6477, 7608, 6837, 2773, 13979, 6252, 2420, 2705, 672, 3297, 5320, 1083, 853, 236, 301, 1237, 706, 4909, 1059, 5995, 1762, 3145, 5848, 1907, 4286, 7167, 922, 610, 2103, 4732, 525, 5382, 4266, 17425, 2835, 14128, 8511, 6195, 14797, 9862, 49384, 16900]

theorem plane488GenLeaf0005 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0005Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0005Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 101
  · exact hroot.hOcc 109
  · exact hroot.hOcc 142
  · exact hroot.hOcc 156
  · exact hroot.hOcc 159
  · exact hroot.hOcc 169
  · exact hroot.hOcc 175
  · exact hroot.hOcc 184
  · exact hroot.hOcc 186
  · exact hroot.hOcc 188
  · exact hroot.hOcc 190
  · exact hroot.hOcc 192
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · exact hroot.hOcc 202
  · exact hroot.hOcc 210
  · exact hroot.hOcc 212
  · exact hroot.hOcc 220
  · exact hroot.hOcc 225
  · exact hroot.hOcc 232
  · exact hroot.hOcc 259
  · exact hroot.hOcc 278
  · exact hroot.hOcc 286
  · exact hroot.hOcc 290
  · exact hroot.hOcc 315
  · exact hroot.hOcc 349
  · exact hroot.hOcc 361
  · exact hroot.hOcc 381
  · exact hroot.hOcc 395
  · exact hroot.hOcc 402
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (25 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (13 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (24 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (23 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23

end QiushiMatmul
