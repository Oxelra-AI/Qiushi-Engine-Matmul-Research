import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0024Refs : Fin 42 → RowRef 413 41 := ![.occ 87, .occ 99, .occ 100, .occ 105, .occ 109, .occ 124, .occ 141, .occ 149, .occ 151, .occ 175, .occ 178, .occ 189, .occ 190, .occ 195, .occ 226, .occ 231, .occ 238, .occ 258, .occ 265, .occ 269, .occ 303, .occ 307, .occ 310, .occ 324, .occ 342, .occ 350, .occ 358, .occ 372, .occ 375, .occ 395, .occ 397, .occ 401, .sumGe, .nonneg 7, .nonneg 8, .branchGe 27 (1), .branchLe 19 (0), .branchLe 16 (0), .branchLe 22 (0), .branchGe 40 (1), .branchLe 35 (0), .branchLe 6 (0)]

def plane488GenLeaf0024Mult : Fin 42 → Nat := ![50, 339, 2787, 3344, 50, 176, 161, 871, 296, 917, 1551, 209, 1003, 457, 956, 1597, 486, 213, 1412, 388, 190, 243, 610, 187, 469, 1563, 272, 771, 176, 816, 707, 816, 3991, 111, 220, 10444, 3284, 3381, 871, 4002, 2787, 3094]

theorem plane488GenLeaf0024 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0024Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0024Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0024Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0024Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 105
  · exact hroot.hOcc 109
  · exact hroot.hOcc 124
  · exact hroot.hOcc 141
  · exact hroot.hOcc 149
  · exact hroot.hOcc 151
  · exact hroot.hOcc 175
  · exact hroot.hOcc 178
  · exact hroot.hOcc 189
  · exact hroot.hOcc 190
  · exact hroot.hOcc 195
  · exact hroot.hOcc 226
  · exact hroot.hOcc 231
  · exact hroot.hOcc 238
  · exact hroot.hOcc 258
  · exact hroot.hOcc 265
  · exact hroot.hOcc 269
  · exact hroot.hOcc 303
  · exact hroot.hOcc 307
  · exact hroot.hOcc 310
  · exact hroot.hOcc 324
  · exact hroot.hOcc 342
  · exact hroot.hOcc 350
  · exact hroot.hOcc 358
  · exact hroot.hOcc 372
  · exact hroot.hOcc 375
  · exact hroot.hOcc 395
  · exact hroot.hOcc 397
  · exact hroot.hOcc 401
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (27 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (16 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (40 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (35 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (6 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6

end QiushiMatmul
