import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0112Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 120, .occ 121, .occ 122, .occ 139, .occ 141, .occ 175, .occ 179, .occ 209, .occ 341, .occ 408, .occ 811, .occ 814, .occ 922, .occ 1143, .occ 1146, .occ 1147, .occ 1168, .occ 1238, .occ 1247, .occ 1382, .occ 1441, .occ 1455, .occ 1458, .occ 1462, .occ 1477, .occ 1537, .occ 1545, .occ 1573, .occ 1597, .occ 1615, .occ 1639, .sumGe, .nonneg 2, .branchLe 15 (0), .branchLe 29 (0), .branchGe 4 (1), .branchGe 36 (1), .branchGe 26 (1), .branchLe 21 (0), .branchLe 18 (0), .branchLe 35 (0), .branchLe 22 (0)]

def plane484GenLeaf0112Mult : Fin 43 → Nat := ![9110, 467, 1401, 12848, 6334, 10206, 20221, 14967, 2152, 4812, 842, 15128, 8180, 15356, 21222, 8086, 2746, 2562, 13356, 5856, 3496, 80, 8308, 1628, 934, 4812, 7748, 5092, 12030, 1002, 1360, 4308, 43926, 4466, 42566, 43926, 143020, 51758, 39670, 32282, 16438, 30894, 30806]

theorem plane484GenLeaf0112 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0112Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0112Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0112Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0112Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 175
  · exact hroot.hOcc 179
  · exact hroot.hOcc 209
  · exact hroot.hOcc 341
  · exact hroot.hOcc 408
  · exact hroot.hOcc 811
  · exact hroot.hOcc 814
  · exact hroot.hOcc 922
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1247
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1441
  · exact hroot.hOcc 1455
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1537
  · exact hroot.hOcc 1545
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1639
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22

end QiushiMatmul
