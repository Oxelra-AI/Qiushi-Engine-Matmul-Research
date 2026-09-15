import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0033Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 93, .occ 113, .occ 126, .occ 136, .occ 155, .occ 166, .occ 169, .occ 178, .occ 210, .occ 213, .occ 218, .occ 228, .occ 233, .occ 238, .occ 245, .occ 253, .occ 265, .occ 276, .occ 279, .occ 285, .occ 301, .occ 304, .occ 312, .occ 331, .occ 336, .occ 355, .occ 356, .occ 367, .occ 368, .occ 369, .occ 392, .occ 399, .occ 413, .sumGe, .nonneg 20, .branchGe 28 (1), .branchLe 19 (0), .branchLe 22 (0), .branchLe 0 (0), .branchGe 35 (1), .branchLe 4 (0)]

def plane485GenLeaf0033Mult : Fin 42 → Nat := ![5801, 1787, 2038, 1185, 2925, 1826, 2839, 4388, 5170, 278, 877, 6, 1587, 2276, 3356, 755, 943, 478, 4435, 4038, 1299, 175, 1740, 2414, 679, 19, 327, 2134, 2379, 257, 1435, 2348, 1444, 775, 10562, 8513, 14463, 8697, 4390, 3182, 28965, 9263]

theorem plane485GenLeaf0033 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0033Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0033Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0033Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0033Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 93
  · exact hroot.hOcc 113
  · exact hroot.hOcc 126
  · exact hroot.hOcc 136
  · exact hroot.hOcc 155
  · exact hroot.hOcc 166
  · exact hroot.hOcc 169
  · exact hroot.hOcc 178
  · exact hroot.hOcc 210
  · exact hroot.hOcc 213
  · exact hroot.hOcc 218
  · exact hroot.hOcc 228
  · exact hroot.hOcc 233
  · exact hroot.hOcc 238
  · exact hroot.hOcc 245
  · exact hroot.hOcc 253
  · exact hroot.hOcc 265
  · exact hroot.hOcc 276
  · exact hroot.hOcc 279
  · exact hroot.hOcc 285
  · exact hroot.hOcc 301
  · exact hroot.hOcc 304
  · exact hroot.hOcc 312
  · exact hroot.hOcc 331
  · exact hroot.hOcc 336
  · exact hroot.hOcc 355
  · exact hroot.hOcc 356
  · exact hroot.hOcc 367
  · exact hroot.hOcc 368
  · exact hroot.hOcc 369
  · exact hroot.hOcc 392
  · exact hroot.hOcc 399
  · exact hroot.hOcc 413
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (28 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (19 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (22 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (0 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (35 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (4 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
