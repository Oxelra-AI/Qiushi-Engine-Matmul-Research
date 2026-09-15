import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0068Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 86, .occ 101, .occ 104, .occ 144, .occ 149, .occ 161, .occ 167, .occ 190, .occ 219, .occ 225, .occ 235, .occ 241, .occ 253, .occ 260, .occ 280, .occ 281, .occ 294, .occ 299, .occ 343, .occ 353, .occ 355, .occ 370, .occ 390, .occ 391, .occ 412, .occ 572, .occ 594, .occ 609, .occ 628, .occ 639, .occ 644, .occ 650, .occ 661, .occ 662, .occ 665, .sumGe, .nonneg 8, .nonneg 22, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchGe 29 (1), .branchLe 10 (0), .branchLe 12 (0), .branchLe 16 (0), .branchLe 20 (0), .branchGe 11 (1)]

def plane487GenLeaf0068Mult : Fin 49 → Nat := ![245, 1040, 4477, 2495, 1706, 1439, 726, 743, 6757, 890, 249, 2299, 3529, 442, 1749, 1191, 1336, 376, 843, 670, 1534, 2588, 419, 1818, 773, 68, 331, 690, 902, 308, 220, 635, 3252, 1176, 1729, 220, 7392, 596, 519, 12291, 4351, 3365, 6490, 18048, 5346, 951, 3612, 6923, 10183]

theorem plane487GenLeaf0068 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0068Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0068Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0068Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0068Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 86
  · exact hroot.hOcc 101
  · exact hroot.hOcc 104
  · exact hroot.hOcc 144
  · exact hroot.hOcc 149
  · exact hroot.hOcc 161
  · exact hroot.hOcc 167
  · exact hroot.hOcc 190
  · exact hroot.hOcc 219
  · exact hroot.hOcc 225
  · exact hroot.hOcc 235
  · exact hroot.hOcc 241
  · exact hroot.hOcc 253
  · exact hroot.hOcc 260
  · exact hroot.hOcc 280
  · exact hroot.hOcc 281
  · exact hroot.hOcc 294
  · exact hroot.hOcc 299
  · exact hroot.hOcc 343
  · exact hroot.hOcc 353
  · exact hroot.hOcc 355
  · exact hroot.hOcc 370
  · exact hroot.hOcc 390
  · exact hroot.hOcc 391
  · exact hroot.hOcc 412
  · exact hroot.hOcc 572
  · exact hroot.hOcc 594
  · exact hroot.hOcc 609
  · exact hroot.hOcc 628
  · exact hroot.hOcc 639
  · exact hroot.hOcc 644
  · exact hroot.hOcc 650
  · exact hroot.hOcc 661
  · exact hroot.hOcc 662
  · exact hroot.hOcc 665
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (22 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (10 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (16 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (20 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (11 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
