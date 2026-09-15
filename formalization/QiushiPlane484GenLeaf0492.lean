import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0492Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 124, .occ 128, .occ 129, .occ 130, .occ 131, .occ 133, .occ 138, .occ 155, .occ 257, .occ 456, .occ 527, .occ 576, .occ 707, .occ 762, .occ 859, .occ 983, .occ 1190, .occ 1191, .occ 1220, .occ 1335, .occ 1353, .occ 1358, .occ 1483, .occ 1564, .occ 1580, .occ 1601, .occ 1602, .occ 1631, .occ 1642, .sumGe, .nonneg 3, .nonneg 16, .nonneg 20, .nonneg 21, .nonneg 23, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchGe 19 (1), .branchGe 28 (1), .branchGe 12 (1)]

def plane484GenLeaf0492Mult : Fin 43 → Nat := ![36, 31, 158, 9, 9, 292, 82, 82, 122, 32, 28, 12, 26, 76, 176, 79, 68, 10, 18, 118, 62, 152, 142, 14, 28, 14, 32, 32, 52, 72, 306, 110, 156, 244, 8, 274, 756, 174, 142, 592, 760, 524, 970]

theorem plane484GenLeaf0492 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0492Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0492Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0492Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0492Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 155
  · exact hroot.hOcc 257
  · exact hroot.hOcc 456
  · exact hroot.hOcc 527
  · exact hroot.hOcc 576
  · exact hroot.hOcc 707
  · exact hroot.hOcc 762
  · exact hroot.hOcc 859
  · exact hroot.hOcc 983
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1335
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1564
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1642
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
