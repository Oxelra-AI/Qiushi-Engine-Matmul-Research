import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0031Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 101, .occ 102, .occ 108, .occ 110, .occ 135, .occ 136, .occ 140, .occ 155, .occ 171, .occ 176, .occ 186, .occ 224, .occ 233, .occ 238, .occ 241, .occ 245, .occ 252, .occ 253, .occ 268, .occ 303, .occ 309, .occ 316, .occ 328, .occ 336, .occ 355, .occ 356, .occ 367, .occ 374, .occ 375, .occ 377, .sumGe, .nonneg 7, .nonneg 12, .nonneg 16, .branchGe 28 (1), .branchLe 19 (0), .branchLe 22 (0), .branchLe 0 (0), .branchLe 35 (0), .branchLe 6 (0), .branchGe 32 (1)]

def plane485GenLeaf0031Mult : Fin 42 → Nat := ![383, 431, 700, 196, 541, 126, 15, 17, 239, 48, 142, 278, 299, 154, 172, 147, 334, 7, 401, 21, 21, 16, 92, 169, 176, 42, 162, 500, 89, 25, 211, 901, 80, 24, 2, 2324, 901, 386, 662, 575, 760, 1808]

theorem plane485GenLeaf0031 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0031Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0031Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0031Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0031Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 140
  · exact hroot.hOcc 155
  · exact hroot.hOcc 171
  · exact hroot.hOcc 176
  · exact hroot.hOcc 186
  · exact hroot.hOcc 224
  · exact hroot.hOcc 233
  · exact hroot.hOcc 238
  · exact hroot.hOcc 241
  · exact hroot.hOcc 245
  · exact hroot.hOcc 252
  · exact hroot.hOcc 253
  · exact hroot.hOcc 268
  · exact hroot.hOcc 303
  · exact hroot.hOcc 309
  · exact hroot.hOcc 316
  · exact hroot.hOcc 328
  · exact hroot.hOcc 336
  · exact hroot.hOcc 355
  · exact hroot.hOcc 356
  · exact hroot.hOcc 367
  · exact hroot.hOcc 374
  · exact hroot.hOcc 375
  · exact hroot.hOcc 377
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (12 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (16 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (28 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (0 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (35 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (6 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (32 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32

end QiushiMatmul
