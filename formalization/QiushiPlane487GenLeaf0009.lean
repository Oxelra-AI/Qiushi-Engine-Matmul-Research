import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0009Refs : Fin 44 → RowRef 668 48 := ![.occ 83, .occ 100, .occ 123, .occ 124, .occ 158, .occ 172, .occ 181, .occ 206, .occ 216, .occ 217, .occ 246, .occ 253, .occ 303, .occ 313, .occ 315, .occ 316, .occ 325, .occ 353, .occ 356, .occ 386, .occ 387, .occ 394, .occ 399, .occ 412, .occ 488, .occ 499, .occ 517, .occ 587, .occ 588, .occ 609, .occ 618, .occ 640, .occ 663, .sumGe, .nonneg 7, .nonneg 8, .nonneg 30, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchLe 25 (0), .branchLe 12 (0), .branchGe 15 (1), .branchGe 40 (1)]

def plane487GenLeaf0009Mult : Fin 44 → Nat := ![1985, 1466, 443, 262, 2415, 807, 2765, 380, 723, 1235, 1131, 665, 1844, 222, 759, 839, 299, 1578, 751, 1582, 299, 1183, 1206, 383, 412, 299, 665, 937, 439, 286, 222, 659, 977, 4440, 2010, 755, 19, 3463, 3242, 4440, 3012, 2595, 9700, 10208]

theorem plane487GenLeaf0009 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0009Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0009Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 100
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 158
  · exact hroot.hOcc 172
  · exact hroot.hOcc 181
  · exact hroot.hOcc 206
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · exact hroot.hOcc 246
  · exact hroot.hOcc 253
  · exact hroot.hOcc 303
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 316
  · exact hroot.hOcc 325
  · exact hroot.hOcc 353
  · exact hroot.hOcc 356
  · exact hroot.hOcc 386
  · exact hroot.hOcc 387
  · exact hroot.hOcc 394
  · exact hroot.hOcc 399
  · exact hroot.hOcc 412
  · exact hroot.hOcc 488
  · exact hroot.hOcc 499
  · exact hroot.hOcc 517
  · exact hroot.hOcc 587
  · exact hroot.hOcc 588
  · exact hroot.hOcc 609
  · exact hroot.hOcc 618
  · exact hroot.hOcc 640
  · exact hroot.hOcc 663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (30 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (15 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (40 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
