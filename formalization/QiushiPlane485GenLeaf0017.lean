import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0017Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 94, .occ 105, .occ 120, .occ 128, .occ 135, .occ 139, .occ 149, .occ 153, .occ 163, .occ 168, .occ 173, .occ 179, .occ 182, .occ 184, .occ 201, .occ 208, .occ 215, .occ 218, .occ 228, .occ 232, .occ 238, .occ 239, .occ 248, .occ 252, .occ 254, .occ 276, .occ 287, .occ 291, .occ 329, .occ 330, .occ 346, .occ 374, .occ 410, .sumGe, .nonneg 0, .branchLe 28 (0), .branchLe 21 (0), .branchGe 14 (1), .branchLe 29 (0), .branchLe 13 (0), .branchGe 15 (1)]

def plane485GenLeaf0017Mult : Fin 42 → Nat := ![32244, 28532, 11007, 2475, 18425, 28686, 9052, 2193, 11016, 7359, 5959, 1055, 5286, 2193, 16879, 16041, 4148, 3175, 1975, 19739, 18150, 1320, 15822, 2326, 2452, 12250, 2725, 17999, 1810, 1789, 5566, 3507, 7687, 383, 39931, 14686, 36636, 34365, 47156, 26012, 23052, 135278]

theorem plane485GenLeaf0017 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0017Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0017Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0017Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0017Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 94
  · exact hroot.hOcc 105
  · exact hroot.hOcc 120
  · exact hroot.hOcc 128
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 149
  · exact hroot.hOcc 153
  · exact hroot.hOcc 163
  · exact hroot.hOcc 168
  · exact hroot.hOcc 173
  · exact hroot.hOcc 179
  · exact hroot.hOcc 182
  · exact hroot.hOcc 184
  · exact hroot.hOcc 201
  · exact hroot.hOcc 208
  · exact hroot.hOcc 215
  · exact hroot.hOcc 218
  · exact hroot.hOcc 228
  · exact hroot.hOcc 232
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 248
  · exact hroot.hOcc 252
  · exact hroot.hOcc 254
  · exact hroot.hOcc 276
  · exact hroot.hOcc 287
  · exact hroot.hOcc 291
  · exact hroot.hOcc 329
  · exact hroot.hOcc 330
  · exact hroot.hOcc 346
  · exact hroot.hOcc 374
  · exact hroot.hOcc 410
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (29 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (13 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (15 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15

end QiushiMatmul
