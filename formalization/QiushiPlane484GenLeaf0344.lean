import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0344Refs : Fin 41 → RowRef 1665 43 := ![.occ 123, .occ 124, .occ 126, .occ 127, .occ 130, .occ 135, .occ 136, .occ 141, .occ 142, .occ 182, .occ 325, .occ 386, .occ 408, .occ 411, .occ 537, .occ 631, .occ 747, .occ 818, .occ 1102, .occ 1173, .occ 1213, .occ 1215, .occ 1229, .occ 1462, .occ 1481, .occ 1567, .occ 1580, .occ 1602, .occ 1632, .occ 1654, .sumGe, .nonneg 15, .nonneg 16, .branchGe 2 (1), .branchLe 23 (0), .branchGe 26 (1), .branchGe 14 (1), .branchLe 36 (0), .branchGe 28 (1), .branchLe 8 (0), .branchLe 5 (0)]

def plane484GenLeaf0344Mult : Fin 41 → Nat := ![8, 8, 46, 54, 92, 67, 7, 17, 15, 96, 98, 56, 16, 88, 102, 86, 18, 60, 46, 44, 20, 16, 36, 14, 90, 30, 50, 60, 46, 28, 228, 16, 16, 228, 54, 416, 790, 164, 400, 220, 220]

theorem plane484GenLeaf0344 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0344Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0344Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0344Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0344Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 182
  · exact hroot.hOcc 325
  · exact hroot.hOcc 386
  · exact hroot.hOcc 408
  · exact hroot.hOcc 411
  · exact hroot.hOcc 537
  · exact hroot.hOcc 631
  · exact hroot.hOcc 747
  · exact hroot.hOcc 818
  · exact hroot.hOcc 1102
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1229
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1632
  · exact hroot.hOcc 1654
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5

end QiushiMatmul
