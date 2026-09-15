import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0043Refs : Fin 47 → RowRef 668 48 := ![.occ 87, .occ 99, .occ 108, .occ 139, .occ 175, .occ 195, .occ 217, .occ 225, .occ 228, .occ 233, .occ 234, .occ 237, .occ 246, .occ 265, .occ 266, .occ 269, .occ 275, .occ 280, .occ 288, .occ 303, .occ 315, .occ 335, .occ 356, .occ 379, .occ 386, .occ 391, .occ 454, .occ 485, .occ 503, .occ 539, .occ 557, .occ 566, .occ 623, .occ 651, .occ 657, .occ 666, .sumGe, .nonneg 8, .nonneg 30, .nonneg 33, .nonneg 38, .branchLe 39 (0), .branchGe 23 (1), .branchGe 2 (1), .branchLe 6 (0), .branchLe 12 (0), .branchLe 14 (0)]

def plane487GenLeaf0043Mult : Fin 47 → Nat := ![6766, 1612, 2972, 9639, 8680, 19671, 2635, 9089, 11911, 5845, 16422, 6106, 2873, 5704, 5301, 99, 12293, 2747, 2418, 2972, 16772, 13839, 2774, 3427, 11527, 6342, 1750, 5694, 779, 8891, 1638, 99, 3468, 6890, 3527, 3111, 33034, 11627, 3111, 2576, 5953, 29507, 139256, 37932, 23813, 11527, 30062]

theorem plane487GenLeaf0043 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0043Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0043Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0043Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0043Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 99
  · exact hroot.hOcc 108
  · exact hroot.hOcc 139
  · exact hroot.hOcc 175
  · exact hroot.hOcc 195
  · exact hroot.hOcc 217
  · exact hroot.hOcc 225
  · exact hroot.hOcc 228
  · exact hroot.hOcc 233
  · exact hroot.hOcc 234
  · exact hroot.hOcc 237
  · exact hroot.hOcc 246
  · exact hroot.hOcc 265
  · exact hroot.hOcc 266
  · exact hroot.hOcc 269
  · exact hroot.hOcc 275
  · exact hroot.hOcc 280
  · exact hroot.hOcc 288
  · exact hroot.hOcc 303
  · exact hroot.hOcc 315
  · exact hroot.hOcc 335
  · exact hroot.hOcc 356
  · exact hroot.hOcc 379
  · exact hroot.hOcc 386
  · exact hroot.hOcc 391
  · exact hroot.hOcc 454
  · exact hroot.hOcc 485
  · exact hroot.hOcc 503
  · exact hroot.hOcc 539
  · exact hroot.hOcc 557
  · exact hroot.hOcc 566
  · exact hroot.hOcc 623
  · exact hroot.hOcc 651
  · exact hroot.hOcc 657
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (30 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (33 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (38 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (2 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (14 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
