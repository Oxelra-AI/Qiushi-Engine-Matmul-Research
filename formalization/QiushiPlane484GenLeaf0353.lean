import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0353Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 124, .occ 132, .occ 272, .occ 386, .occ 1143, .occ 1146, .occ 1151, .occ 1154, .occ 1172, .occ 1179, .occ 1186, .occ 1190, .occ 1213, .occ 1216, .occ 1228, .occ 1252, .occ 1256, .occ 1357, .occ 1358, .occ 1370, .occ 1458, .occ 1459, .occ 1477, .occ 1501, .occ 1505, .occ 1567, .occ 1573, .occ 1603, .occ 1606, .sumGe, .nonneg 26, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchLe 35 (0), .branchLe 3 (0), .branchLe 24 (0), .branchLe 18 (0), .branchLe 19 (0), .branchLe 14 (0), .branchLe 8 (0), .branchGe 38 (1)]

def plane484GenLeaf0353Mult : Fin 44 → Nat := ![6330, 4010, 5312, 3392, 14060, 1087, 6680, 1028, 244, 804, 6053, 390, 2586, 2345, 5013, 1872, 3646, 1580, 157, 2186, 6694, 1118, 7162, 4828, 120, 400, 300, 4413, 1054, 1922, 22778, 7388, 20592, 10748, 18768, 44148, 7488, 11796, 14300, 7320, 21360, 13276, 22388, 17604]

theorem plane484GenLeaf0353 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0353Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0353Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0353Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0353Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 132
  · exact hroot.hOcc 272
  · exact hroot.hOcc 386
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1228
  · exact hroot.hOcc 1252
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1370
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1501
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1606
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
