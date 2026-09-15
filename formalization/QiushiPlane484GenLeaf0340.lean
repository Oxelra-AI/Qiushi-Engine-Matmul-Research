import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0340Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 123, .occ 137, .occ 138, .occ 140, .occ 142, .occ 210, .occ 246, .occ 346, .occ 411, .occ 816, .occ 1063, .occ 1146, .occ 1147, .occ 1158, .occ 1187, .occ 1214, .occ 1216, .occ 1276, .occ 1334, .occ 1472, .occ 1491, .occ 1504, .occ 1571, .occ 1573, .occ 1597, .occ 1603, .sumGe, .nonneg 3, .nonneg 11, .nonneg 15, .nonneg 24, .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchGe 26 (1), .branchLe 14 (0), .branchGe 1 (1), .branchGe 30 (1), .branchGe 36 (1), .branchLe 18 (0), .branchGe 6 (1)]

def plane484GenLeaf0340Mult : Fin 43 → Nat := ![7, 60, 9, 21, 1, 28, 21, 1, 5, 18, 4, 8, 24, 21, 11, 31, 4, 4, 5, 7, 1, 17, 47, 40, 1, 13, 5, 9, 73, 37, 7, 16, 6, 55, 72, 6, 154, 73, 41, 99, 113, 32, 209]

theorem plane484GenLeaf0340 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0340Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0340Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0340Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0340Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 210
  · exact hroot.hOcc 246
  · exact hroot.hOcc 346
  · exact hroot.hOcc 411
  · exact hroot.hOcc 816
  · exact hroot.hOcc 1063
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1276
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1504
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1603
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
