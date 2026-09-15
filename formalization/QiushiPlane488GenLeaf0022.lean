import QiushiPlane488GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane488GenLeaf0022Refs : Fin 42 → RowRef 413 41 := ![.occ 92, .occ 96, .occ 98, .occ 104, .occ 106, .occ 108, .occ 110, .occ 112, .occ 119, .occ 156, .occ 161, .occ 174, .occ 183, .occ 184, .occ 189, .occ 218, .occ 224, .occ 239, .occ 251, .occ 252, .occ 265, .occ 288, .occ 319, .occ 326, .occ 337, .occ 340, .occ 342, .occ 352, .occ 367, .occ 375, .occ 386, .occ 393, .occ 395, .occ 409, .sumGe, .nonneg 0, .nonneg 8, .nonneg 17, .branchLe 27 (0), .branchGe 15 (1), .branchGe 14 (1), .branchGe 28 (1)]

def plane488GenLeaf0022Mult : Fin 42 → Nat := ![1194, 155, 223, 626, 876, 399, 1056, 1602, 656, 2670, 390, 60, 366, 1594, 1563, 2093, 855, 518, 474, 163, 155, 269, 1173, 458, 458, 119, 655, 908, 642, 337, 60, 642, 252, 252, 3312, 2333, 1254, 589, 2657, 9405, 7345, 5642]

theorem plane488GenLeaf0022 (x : Fin 41 → Int)
    (hroot : plane488GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane488GenLeaf0022Refs i).resolveCoeff plane488GenOccSys j)
    (fun i => (plane488GenLeaf0022Refs i).resolveRhs plane488GenOccSys) plane488GenLeaf0022Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane488GenLeaf0022Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 92
  · exact hroot.hOcc 96
  · exact hroot.hOcc 98
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 119
  · exact hroot.hOcc 156
  · exact hroot.hOcc 161
  · exact hroot.hOcc 174
  · exact hroot.hOcc 183
  · exact hroot.hOcc 184
  · exact hroot.hOcc 189
  · exact hroot.hOcc 218
  · exact hroot.hOcc 224
  · exact hroot.hOcc 239
  · exact hroot.hOcc 251
  · exact hroot.hOcc 252
  · exact hroot.hOcc 265
  · exact hroot.hOcc 288
  · exact hroot.hOcc 319
  · exact hroot.hOcc 326
  · exact hroot.hOcc 337
  · exact hroot.hOcc 340
  · exact hroot.hOcc 342
  · exact hroot.hOcc 352
  · exact hroot.hOcc 367
  · exact hroot.hOcc 375
  · exact hroot.hOcc 386
  · exact hroot.hOcc 393
  · exact hroot.hOcc 395
  · exact hroot.hOcc 409
  · change (∑ j, (-1 : Int) * x j) ≤ -plane488GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (8 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (17 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (27 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (15 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (14 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (28 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
