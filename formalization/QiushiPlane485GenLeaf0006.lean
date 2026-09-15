import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0006Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 99, .occ 100, .occ 118, .occ 132, .occ 139, .occ 155, .occ 163, .occ 173, .occ 177, .occ 188, .occ 195, .occ 213, .occ 214, .occ 218, .occ 223, .occ 228, .occ 236, .occ 252, .occ 257, .occ 279, .occ 287, .occ 298, .occ 305, .occ 352, .occ 353, .occ 359, .occ 360, .occ 362, .occ 372, .occ 374, .occ 392, .sumGe, .nonneg 19, .branchLe 28 (0), .branchLe 21 (0), .branchLe 14 (0), .branchLe 11 (0), .branchGe 39 (1), .branchLe 29 (0), .branchLe 18 (0), .branchGe 26 (1)]

def plane485GenLeaf0006Mult : Fin 42 → Nat := ![6932, 7407, 7493, 3735, 540, 1018, 1490, 225, 1883, 710, 962, 2991, 1034, 410, 6278, 2375, 2891, 261, 2361, 22, 1260, 596, 898, 4379, 642, 678, 4717, 1048, 283, 566, 1598, 566, 9096, 2891, 1558, 4497, 3744, 8247, 16276, 7498, 69, 40361]

theorem plane485GenLeaf0006 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0006Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0006Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 118
  · exact hroot.hOcc 132
  · exact hroot.hOcc 139
  · exact hroot.hOcc 155
  · exact hroot.hOcc 163
  · exact hroot.hOcc 173
  · exact hroot.hOcc 177
  · exact hroot.hOcc 188
  · exact hroot.hOcc 195
  · exact hroot.hOcc 213
  · exact hroot.hOcc 214
  · exact hroot.hOcc 218
  · exact hroot.hOcc 223
  · exact hroot.hOcc 228
  · exact hroot.hOcc 236
  · exact hroot.hOcc 252
  · exact hroot.hOcc 257
  · exact hroot.hOcc 279
  · exact hroot.hOcc 287
  · exact hroot.hOcc 298
  · exact hroot.hOcc 305
  · exact hroot.hOcc 352
  · exact hroot.hOcc 353
  · exact hroot.hOcc 359
  · exact hroot.hOcc 360
  · exact hroot.hOcc 362
  · exact hroot.hOcc 372
  · exact hroot.hOcc 374
  · exact hroot.hOcc 392
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (39 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (29 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (18 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (26 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
