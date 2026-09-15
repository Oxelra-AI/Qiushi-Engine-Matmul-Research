import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0004Refs : Fin 39 → RowRef 413 41 := ![.occ 88, .occ 91, .occ 98, .occ 100, .occ 103, .occ 120, .occ 143, .occ 156, .occ 158, .occ 160, .occ 166, .occ 173, .occ 184, .occ 186, .occ 190, .occ 203, .occ 210, .occ 212, .occ 214, .occ 224, .occ 229, .occ 232, .occ 240, .occ 272, .occ 300, .occ 331, .occ 349, .occ 355, .occ 362, .occ 404, .sumGe, .nonneg 0, .branchLe 27 (0), .branchLe 15 (0), .branchLe 20 (0), .branchLe 25 (0), .branchLe 13 (0), .branchLe 24 (0), .branchGe 16 (1)]

def plane488GenLeaf0004Mult : Fin 39 → Nat := ![481, 786, 257, 80, 640, 450, 522, 1083, 210, 498, 111, 675, 455, 35, 261, 767, 925, 1359, 391, 194, 481, 329, 198, 296, 58, 74, 964, 1260, 250, 724, 2474, 597, 1082, 1317, 1421, 761, 1928, 786, 7066]

theorem plane488GenLeaf0004 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0004Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0004Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 88
  · exact hroot.hOcc 91
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 120
  · exact hroot.hOcc 143
  · exact hroot.hOcc 156
  · exact hroot.hOcc 158
  · exact hroot.hOcc 160
  · exact hroot.hOcc 166
  · exact hroot.hOcc 173
  · exact hroot.hOcc 184
  · exact hroot.hOcc 186
  · exact hroot.hOcc 190
  · exact hroot.hOcc 203
  · exact hroot.hOcc 210
  · exact hroot.hOcc 212
  · exact hroot.hOcc 214
  · exact hroot.hOcc 224
  · exact hroot.hOcc 229
  · exact hroot.hOcc 232
  · exact hroot.hOcc 240
  · exact hroot.hOcc 272
  · exact hroot.hOcc 300
  · exact hroot.hOcc 331
  · exact hroot.hOcc 349
  · exact hroot.hOcc 355
  · exact hroot.hOcc 362
  · exact hroot.hOcc 404
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (25 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (13 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (24 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (16 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
