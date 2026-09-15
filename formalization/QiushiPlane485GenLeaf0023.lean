import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0023Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 135, .occ 145, .occ 147, .occ 150, .occ 152, .occ 153, .occ 155, .occ 162, .occ 175, .occ 184, .occ 195, .occ 207, .occ 210, .occ 213, .occ 218, .occ 224, .occ 228, .occ 257, .occ 258, .occ 259, .occ 262, .occ 276, .occ 287, .occ 297, .occ 312, .occ 347, .occ 353, .occ 368, .occ 369, .occ 377, .occ 387, .sumGe, .nonneg 0, .nonneg 4, .nonneg 7, .branchLe 28 (0), .branchGe 21 (1), .branchLe 32 (0), .branchLe 25 (0), .branchGe 23 (1), .branchLe 9 (0)]

def plane485GenLeaf0023Mult : Fin 42 → Nat := ![102984, 51046, 53932, 48496, 952, 29156, 23220, 44932, 125484, 74688, 26013, 39512, 64151, 83326, 7509, 42314, 3215, 61423, 32384, 45180, 12780, 56895, 77221, 78429, 44612, 42560, 18136, 25128, 38032, 14552, 41856, 50530, 243952, 149024, 8236, 43412, 107198, 277022, 163516, 116014, 366938, 243952]

theorem plane485GenLeaf0023 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0023Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0023Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0023Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0023Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 135
  · exact hroot.hOcc 145
  · exact hroot.hOcc 147
  · exact hroot.hOcc 150
  · exact hroot.hOcc 152
  · exact hroot.hOcc 153
  · exact hroot.hOcc 155
  · exact hroot.hOcc 162
  · exact hroot.hOcc 175
  · exact hroot.hOcc 184
  · exact hroot.hOcc 195
  · exact hroot.hOcc 207
  · exact hroot.hOcc 210
  · exact hroot.hOcc 213
  · exact hroot.hOcc 218
  · exact hroot.hOcc 224
  · exact hroot.hOcc 228
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 259
  · exact hroot.hOcc 262
  · exact hroot.hOcc 276
  · exact hroot.hOcc 287
  · exact hroot.hOcc 297
  · exact hroot.hOcc 312
  · exact hroot.hOcc 347
  · exact hroot.hOcc 353
  · exact hroot.hOcc 368
  · exact hroot.hOcc 369
  · exact hroot.hOcc 377
  · exact hroot.hOcc 387
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (4 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (32 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (25 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (23 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (9 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
