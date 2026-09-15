import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0034Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 93, .occ 95, .occ 102, .occ 124, .occ 135, .occ 140, .occ 156, .occ 169, .occ 171, .occ 178, .occ 179, .occ 181, .occ 182, .occ 207, .occ 228, .occ 233, .occ 238, .occ 246, .occ 265, .occ 268, .occ 273, .occ 279, .occ 299, .occ 301, .occ 304, .occ 338, .occ 367, .occ 368, .occ 392, .occ 396, .occ 407, .occ 413, .sumGe, .nonneg 20, .nonneg 23, .branchGe 28 (1), .branchLe 19 (0), .branchLe 22 (0), .branchLe 0 (0), .branchGe 35 (1), .branchGe 4 (1)]

def plane485GenLeaf0034Mult : Fin 42 → Nat := ![311, 826, 390, 1141, 2839, 3190, 950, 1058, 3843, 16, 3754, 42, 5958, 4681, 917, 1533, 1133, 618, 218, 271, 214, 775, 2041, 1909, 806, 1317, 111, 1093, 390, 796, 598, 2843, 216, 7091, 6008, 390, 11688, 5187, 369, 2441, 25121, 13921]

theorem plane485GenLeaf0034 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0034Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0034Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0034Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0034Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 102
  · exact hroot.hOcc 124
  · exact hroot.hOcc 135
  · exact hroot.hOcc 140
  · exact hroot.hOcc 156
  · exact hroot.hOcc 169
  · exact hroot.hOcc 171
  · exact hroot.hOcc 178
  · exact hroot.hOcc 179
  · exact hroot.hOcc 181
  · exact hroot.hOcc 182
  · exact hroot.hOcc 207
  · exact hroot.hOcc 228
  · exact hroot.hOcc 233
  · exact hroot.hOcc 238
  · exact hroot.hOcc 246
  · exact hroot.hOcc 265
  · exact hroot.hOcc 268
  · exact hroot.hOcc 273
  · exact hroot.hOcc 279
  · exact hroot.hOcc 299
  · exact hroot.hOcc 301
  · exact hroot.hOcc 304
  · exact hroot.hOcc 338
  · exact hroot.hOcc 367
  · exact hroot.hOcc 368
  · exact hroot.hOcc 392
  · exact hroot.hOcc 396
  · exact hroot.hOcc 407
  · exact hroot.hOcc 413
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (23 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (28 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (0 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (35 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (4 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
