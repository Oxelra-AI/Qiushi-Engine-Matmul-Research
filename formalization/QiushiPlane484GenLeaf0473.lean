import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0473Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 123, .occ 124, .occ 129, .occ 130, .occ 140, .occ 142, .occ 163, .occ 290, .occ 545, .occ 615, .occ 738, .occ 1081, .occ 1101, .occ 1136, .occ 1166, .occ 1188, .occ 1189, .occ 1191, .occ 1198, .occ 1200, .occ 1458, .occ 1459, .occ 1467, .occ 1484, .occ 1529, .occ 1536, .occ 1615, .occ 1626, .occ 1641, .occ 1646, .sumGe, .nonneg 7, .nonneg 22, .nonneg 25, .branchGe 15 (1), .branchLe 35 (0), .branchGe 0 (1), .branchLe 19 (0), .branchLe 3 (0), .branchLe 38 (0), .branchLe 20 (0), .branchGe 27 (1), .branchGe 13 (1)]

def plane484GenLeaf0473Mult : Fin 44 → Nat := ![192, 55, 69, 465, 386, 236, 638, 736, 69, 110, 139, 137, 83, 17, 39, 245, 88, 101, 252, 12, 157, 67, 330, 254, 102, 22, 157, 206, 176, 121, 139, 1096, 254, 315, 60, 1934, 994, 1267, 957, 254, 994, 582, 1219, 2457]

theorem plane484GenLeaf0473 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0473Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0473Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0473Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0473Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 163
  · exact hroot.hOcc 290
  · exact hroot.hOcc 545
  · exact hroot.hOcc 615
  · exact hroot.hOcc 738
  · exact hroot.hOcc 1081
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1189
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1198
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1536
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1641
  · exact hroot.hOcc 1646
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
