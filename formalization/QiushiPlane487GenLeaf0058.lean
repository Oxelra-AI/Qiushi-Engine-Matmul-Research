import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0058Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 92, .occ 99, .occ 104, .occ 111, .occ 153, .occ 160, .occ 169, .occ 185, .occ 195, .occ 211, .occ 234, .occ 239, .occ 241, .occ 256, .occ 260, .occ 294, .occ 298, .occ 312, .occ 315, .occ 347, .occ 356, .occ 364, .occ 377, .occ 379, .occ 391, .occ 429, .occ 430, .occ 523, .occ 527, .occ 578, .occ 590, .occ 650, .occ 653, .occ 660, .occ 662, .sumGe, .nonneg 19, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 36 (0), .branchGe 23 (1), .branchLe 10 (0), .branchLe 16 (0), .branchLe 20 (0), .branchGe 33 (1)]

def plane487GenLeaf0058Mult : Fin 49 → Nat := ![13112, 19979, 8504, 5914, 11784, 4540, 3426, 17213, 1362, 5959, 7160, 7581, 10745, 3523, 8304, 778, 1656, 7581, 5473, 10713, 1348, 6534, 617, 2843, 5015, 7659, 1726, 723, 3871, 1188, 1844, 2367, 2648, 3352, 1113, 8429, 26693, 816, 4581, 8554, 6406, 16807, 6952, 24045, 63816, 22228, 25915, 21220, 56447]

theorem plane487GenLeaf0058 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0058Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0058Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0058Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0058Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 92
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 111
  · exact hroot.hOcc 153
  · exact hroot.hOcc 160
  · exact hroot.hOcc 169
  · exact hroot.hOcc 185
  · exact hroot.hOcc 195
  · exact hroot.hOcc 211
  · exact hroot.hOcc 234
  · exact hroot.hOcc 239
  · exact hroot.hOcc 241
  · exact hroot.hOcc 256
  · exact hroot.hOcc 260
  · exact hroot.hOcc 294
  · exact hroot.hOcc 298
  · exact hroot.hOcc 312
  · exact hroot.hOcc 315
  · exact hroot.hOcc 347
  · exact hroot.hOcc 356
  · exact hroot.hOcc 364
  · exact hroot.hOcc 377
  · exact hroot.hOcc 379
  · exact hroot.hOcc 391
  · exact hroot.hOcc 429
  · exact hroot.hOcc 430
  · exact hroot.hOcc 523
  · exact hroot.hOcc 527
  · exact hroot.hOcc 578
  · exact hroot.hOcc 590
  · exact hroot.hOcc 650
  · exact hroot.hOcc 653
  · exact hroot.hOcc 660
  · exact hroot.hOcc 662
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (23 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (10 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (16 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (20 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (33 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
