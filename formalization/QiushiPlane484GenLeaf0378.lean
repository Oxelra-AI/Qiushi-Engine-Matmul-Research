import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0378Refs : Fin 44 → RowRef 1665 43 := ![.occ 124, .occ 125, .occ 131, .occ 132, .occ 137, .occ 242, .occ 305, .occ 331, .occ 349, .occ 1144, .occ 1146, .occ 1147, .occ 1164, .occ 1166, .occ 1172, .occ 1191, .occ 1213, .occ 1214, .occ 1220, .occ 1221, .occ 1223, .occ 1263, .occ 1313, .occ 1462, .occ 1481, .occ 1539, .occ 1565, .occ 1571, .occ 1597, .occ 1623, .occ 1649, .occ 1655, .sumGe, .nonneg 6, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchLe 30 (0), .branchLe 42 (0), .branchGe 27 (1), .branchLe 9 (0), .branchGe 28 (1)]

def plane484GenLeaf0378Mult : Fin 44 → Nat := ![10855, 8550, 5800, 14992, 4856, 5810, 6276, 8709, 3338, 3199, 15010, 4439, 2878, 3514, 1005, 1761, 10696, 228, 3289, 50, 583, 2969, 3742, 777, 2928, 1400, 4106, 3997, 8293, 1450, 12123, 811, 32928, 94, 27128, 26773, 10234, 61775, 36094, 29639, 29223, 35360, 24378, 45093]

theorem plane484GenLeaf0378 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0378Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0378Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0378Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0378Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 242
  · exact hroot.hOcc 305
  · exact hroot.hOcc 331
  · exact hroot.hOcc 349
  · exact hroot.hOcc 1144
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1221
  · exact hroot.hOcc 1223
  · exact hroot.hOcc 1263
  · exact hroot.hOcc 1313
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1539
  · exact hroot.hOcc 1565
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1649
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
