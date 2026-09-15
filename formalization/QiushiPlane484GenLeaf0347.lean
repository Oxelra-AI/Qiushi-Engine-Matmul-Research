import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0347Refs : Fin 43 → RowRef 1665 43 := ![.occ 125, .occ 128, .occ 130, .occ 137, .occ 138, .occ 141, .occ 142, .occ 219, .occ 387, .occ 747, .occ 819, .occ 1179, .occ 1191, .occ 1214, .occ 1215, .occ 1216, .occ 1231, .occ 1233, .occ 1303, .occ 1311, .occ 1341, .occ 1353, .occ 1462, .occ 1483, .occ 1496, .occ 1527, .occ 1567, .occ 1601, .occ 1640, .occ 1661, .sumGe, .nonneg 15, .nonneg 19, .nonneg 20, .nonneg 23, .nonneg 32, .branchGe 2 (1), .branchLe 7 (0), .branchGe 26 (1), .branchGe 14 (1), .branchGe 36 (1), .branchLe 30 (0), .branchLe 6 (0)]

def plane484GenLeaf0347Mult : Fin 43 → Nat := ![198, 4, 80, 173, 129, 69, 39, 40, 14, 2, 40, 58, 44, 14, 62, 18, 38, 88, 18, 84, 2, 4, 180, 10, 18, 80, 24, 102, 16, 6, 318, 58, 70, 44, 66, 8, 294, 318, 592, 724, 354, 318, 318]

theorem plane484GenLeaf0347 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0347Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0347Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0347Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0347Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 219
  · exact hroot.hOcc 387
  · exact hroot.hOcc 747
  · exact hroot.hOcc 819
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1231
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1311
  · exact hroot.hOcc 1341
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1527
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1640
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6

end QiushiMatmul
