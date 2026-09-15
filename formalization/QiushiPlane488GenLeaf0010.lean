import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0010Refs : Fin 42 → RowRef 413 41 := ![.occ 90, .occ 127, .occ 140, .occ 144, .occ 159, .occ 173, .occ 174, .occ 181, .occ 184, .occ 185, .occ 187, .occ 190, .occ 192, .occ 210, .occ 212, .occ 214, .occ 216, .occ 236, .occ 241, .occ 244, .occ 248, .occ 259, .occ 265, .occ 268, .occ 272, .occ 278, .occ 283, .occ 301, .occ 314, .occ 323, .occ 374, .occ 376, .occ 381, .occ 386, .occ 387, .sumGe, .branchLe 27 (0), .branchLe 15 (0), .branchLe 20 (0), .branchGe 25 (1), .branchLe 1 (0), .branchGe 6 (1)]

def plane488GenLeaf0010Mult : Fin 42 → Nat := ![9542, 3022, 4204, 2004, 7336, 1176, 3302, 6430, 6546, 1723, 1135, 1950, 9481, 7426, 3408, 6017, 1371, 4153, 7671, 5928, 1004, 6520, 2721, 14310, 2284, 920, 1001, 3213, 134, 799, 5302, 33, 3085, 743, 1370, 20064, 15911, 19060, 15392, 30967, 20064, 44991]

theorem plane488GenLeaf0010 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0010Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0010Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 127
  · exact hroot.hOcc 140
  · exact hroot.hOcc 144
  · exact hroot.hOcc 159
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 181
  · exact hroot.hOcc 184
  · exact hroot.hOcc 185
  · exact hroot.hOcc 187
  · exact hroot.hOcc 190
  · exact hroot.hOcc 192
  · exact hroot.hOcc 210
  · exact hroot.hOcc 212
  · exact hroot.hOcc 214
  · exact hroot.hOcc 216
  · exact hroot.hOcc 236
  · exact hroot.hOcc 241
  · exact hroot.hOcc 244
  · exact hroot.hOcc 248
  · exact hroot.hOcc 259
  · exact hroot.hOcc 265
  · exact hroot.hOcc 268
  · exact hroot.hOcc 272
  · exact hroot.hOcc 278
  · exact hroot.hOcc 283
  · exact hroot.hOcc 301
  · exact hroot.hOcc 314
  · exact hroot.hOcc 323
  · exact hroot.hOcc 374
  · exact hroot.hOcc 376
  · exact hroot.hOcc 381
  · exact hroot.hOcc 386
  · exact hroot.hOcc 387
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (25 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (1 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (6 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
