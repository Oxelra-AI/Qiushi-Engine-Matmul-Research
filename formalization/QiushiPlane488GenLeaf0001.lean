import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0001Refs : Fin 42 → RowRef 413 41 := ![.occ 86, .occ 91, .occ 98, .occ 100, .occ 104, .occ 121, .occ 133, .occ 148, .occ 152, .occ 154, .occ 157, .occ 158, .occ 168, .occ 184, .occ 186, .occ 190, .occ 203, .occ 229, .occ 241, .occ 252, .occ 259, .occ 278, .occ 295, .occ 308, .occ 309, .occ 341, .occ 364, .occ 375, .occ 382, .occ 395, .sumGe, .nonneg 0, .branchLe 27 (0), .branchLe 15 (0), .branchLe 20 (0), .branchLe 25 (0), .branchLe 13 (0), .branchLe 24 (0), .branchLe 16 (0), .branchLe 4 (0), .branchLe 37 (0), .branchGe 5 (1)]

def plane488GenLeaf0001Mult : Fin 42 → Nat := ![21, 34, 16, 32, 42, 4, 11, 15, 4, 32, 15, 3, 14, 13, 36, 3, 42, 18, 12, 27, 26, 11, 4, 2, 13, 14, 20, 7, 3, 19, 79, 43, 79, 79, 58, 67, 49, 53, 34, 28, 79, 127]

theorem plane488GenLeaf0001 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0001Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0001Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 91
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 121
  · exact hroot.hOcc 133
  · exact hroot.hOcc 148
  · exact hroot.hOcc 152
  · exact hroot.hOcc 154
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 168
  · exact hroot.hOcc 184
  · exact hroot.hOcc 186
  · exact hroot.hOcc 190
  · exact hroot.hOcc 203
  · exact hroot.hOcc 229
  · exact hroot.hOcc 241
  · exact hroot.hOcc 252
  · exact hroot.hOcc 259
  · exact hroot.hOcc 278
  · exact hroot.hOcc 295
  · exact hroot.hOcc 308
  · exact hroot.hOcc 309
  · exact hroot.hOcc 341
  · exact hroot.hOcc 364
  · exact hroot.hOcc 375
  · exact hroot.hOcc 382
  · exact hroot.hOcc 395
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (20 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (25 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (13 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (24 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (16 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (4 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (37 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (5 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
