import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0027Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 92, .occ 101, .occ 102, .occ 132, .occ 145, .occ 146, .occ 152, .occ 169, .occ 171, .occ 177, .occ 186, .occ 188, .occ 193, .occ 205, .occ 213, .occ 218, .occ 257, .occ 265, .occ 279, .occ 316, .occ 338, .occ 352, .occ 353, .occ 357, .occ 367, .occ 369, .occ 372, .occ 381, .occ 388, .sumGe, .nonneg 23, .branchGe 28 (1), .branchLe 19 (0), .branchLe 22 (0), .branchLe 0 (0), .branchLe 35 (0), .branchLe 6 (0), .branchLe 32 (0), .branchLe 29 (0), .branchLe 14 (0), .branchLe 11 (0)]

def plane485GenLeaf0027Mult : Fin 42 → Nat := ![18124, 3447, 5265, 16988, 1131, 1919, 7395, 18872, 3277, 14113, 10476, 3544, 1131, 10086, 11334, 2847, 13683, 3377, 5082, 3199, 5224, 3812, 846, 2882, 9866, 5525, 2432, 2516, 1354, 9106, 32961, 21103, 75387, 29149, 26034, 17119, 26485, 28013, 23095, 32961, 16216, 30445]

theorem plane485GenLeaf0027 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0027Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0027Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0027Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0027Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 92
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 132
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 152
  · exact hroot.hOcc 169
  · exact hroot.hOcc 171
  · exact hroot.hOcc 177
  · exact hroot.hOcc 186
  · exact hroot.hOcc 188
  · exact hroot.hOcc 193
  · exact hroot.hOcc 205
  · exact hroot.hOcc 213
  · exact hroot.hOcc 218
  · exact hroot.hOcc 257
  · exact hroot.hOcc 265
  · exact hroot.hOcc 279
  · exact hroot.hOcc 316
  · exact hroot.hOcc 338
  · exact hroot.hOcc 352
  · exact hroot.hOcc 353
  · exact hroot.hOcc 357
  · exact hroot.hOcc 367
  · exact hroot.hOcc 369
  · exact hroot.hOcc 372
  · exact hroot.hOcc 381
  · exact hroot.hOcc 388
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (23 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (28 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (0 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (35 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (6 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (32 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (29 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11

end QiushiMatmul
