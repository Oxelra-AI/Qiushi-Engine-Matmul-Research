import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0322Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 123, .occ 142, .occ 325, .occ 581, .occ 953, .occ 968, .occ 991, .occ 1081, .occ 1145, .occ 1146, .occ 1147, .occ 1154, .occ 1168, .occ 1172, .occ 1173, .occ 1216, .occ 1242, .occ 1344, .occ 1440, .occ 1453, .occ 1492, .occ 1496, .occ 1520, .occ 1563, .occ 1573, .occ 1603, .occ 1607, .occ 1608, .occ 1609, .sumGe, .nonneg 9, .nonneg 15, .nonneg 18, .nonneg 21, .nonneg 23, .nonneg 25, .branchGe 2 (1), .branchLe 7 (0), .branchGe 26 (1), .branchLe 14 (0), .branchGe 22 (1), .branchGe 0 (1)]

def plane484GenLeaf0322Mult : Fin 43 → Nat := ![22, 22, 92, 92, 88, 19, 11, 10, 13, 2, 31, 11, 4, 21, 2, 18, 14, 14, 4, 22, 3, 2, 14, 17, 3, 14, 26, 8, 13, 4, 92, 4, 296, 4, 46, 70, 60, 96, 56, 422, 72, 346, 128]

theorem plane484GenLeaf0322 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0322Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0322Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0322Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0322Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 142
  · exact hroot.hOcc 325
  · exact hroot.hOcc 581
  · exact hroot.hOcc 953
  · exact hroot.hOcc 968
  · exact hroot.hOcc 991
  · exact hroot.hOcc 1081
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1242
  · exact hroot.hOcc 1344
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1453
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1520
  · exact hroot.hOcc 1563
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1609
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
