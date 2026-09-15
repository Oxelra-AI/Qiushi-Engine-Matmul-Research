import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0019Refs : Fin 49 → RowRef 668 48 := ![.occ 85, .occ 92, .occ 95, .occ 107, .occ 108, .occ 155, .occ 168, .occ 180, .occ 217, .occ 230, .occ 233, .occ 246, .occ 252, .occ 253, .occ 257, .occ 269, .occ 288, .occ 292, .occ 303, .occ 305, .occ 313, .occ 315, .occ 377, .occ 391, .occ 394, .occ 397, .occ 399, .occ 402, .occ 488, .occ 495, .occ 521, .occ 522, .occ 576, .occ 604, .occ 608, .occ 615, .occ 616, .occ 618, .occ 645, .sumGe, .nonneg 8, .nonneg 27, .nonneg 31, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchGe 25 (1), .branchGe 1 (1), .branchGe 35 (1)]

def plane487GenLeaf0019Mult : Fin 49 → Nat := ![16649, 9425, 11810, 9408, 3729, 7944, 9228, 5497, 1650, 16722, 1109, 5700, 10516, 546, 4439, 1986, 5867, 4109, 3818, 292, 2414, 1030, 169, 9329, 4707, 4812, 9117, 5678, 1950, 87, 2540, 549, 2709, 2943, 1539, 892, 3532, 3706, 5503, 22248, 3750, 1506, 1865, 16453, 5652, 21356, 67555, 39364, 60097]

theorem plane487GenLeaf0019 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0019Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0019Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0019Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0019Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 155
  · exact hroot.hOcc 168
  · exact hroot.hOcc 180
  · exact hroot.hOcc 217
  · exact hroot.hOcc 230
  · exact hroot.hOcc 233
  · exact hroot.hOcc 246
  · exact hroot.hOcc 252
  · exact hroot.hOcc 253
  · exact hroot.hOcc 257
  · exact hroot.hOcc 269
  · exact hroot.hOcc 288
  · exact hroot.hOcc 292
  · exact hroot.hOcc 303
  · exact hroot.hOcc 305
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 377
  · exact hroot.hOcc 391
  · exact hroot.hOcc 394
  · exact hroot.hOcc 397
  · exact hroot.hOcc 399
  · exact hroot.hOcc 402
  · exact hroot.hOcc 488
  · exact hroot.hOcc 495
  · exact hroot.hOcc 521
  · exact hroot.hOcc 522
  · exact hroot.hOcc 576
  · exact hroot.hOcc 604
  · exact hroot.hOcc 608
  · exact hroot.hOcc 615
  · exact hroot.hOcc 616
  · exact hroot.hOcc 618
  · exact hroot.hOcc 645
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (27 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (31 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (1 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (35 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
