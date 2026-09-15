import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0358Refs : Fin 44 → RowRef 1665 43 := ![.occ 92, .occ 122, .occ 125, .occ 128, .occ 129, .occ 131, .occ 133, .occ 137, .occ 138, .occ 257, .occ 348, .occ 446, .occ 785, .occ 791, .occ 859, .occ 1147, .occ 1166, .occ 1186, .occ 1187, .occ 1191, .occ 1301, .occ 1342, .occ 1486, .occ 1489, .occ 1526, .occ 1602, .occ 1608, .occ 1615, .occ 1629, .occ 1652, .occ 1660, .sumGe, .nonneg 9, .nonneg 15, .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchLe 35 (0), .branchLe 3 (0), .branchLe 24 (0), .branchLe 18 (0), .branchGe 19 (1), .branchGe 28 (1), .branchGe 8 (1)]

def plane484GenLeaf0358Mult : Fin 44 → Nat := ![702, 1289, 3141, 953, 326, 2562, 1062, 1034, 2416, 4298, 300, 1558, 86, 150, 1667, 848, 534, 374, 2930, 998, 1312, 210, 820, 998, 150, 392, 2242, 242, 1368, 1868, 242, 6540, 2812, 3220, 8686, 2618, 8774, 5510, 150, 3052, 4124, 12092, 5938, 18764]

theorem plane484GenLeaf0358 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0358Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0358Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0358Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0358Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 92
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 257
  · exact hroot.hOcc 348
  · exact hroot.hOcc 446
  · exact hroot.hOcc 785
  · exact hroot.hOcc 791
  · exact hroot.hOcc 859
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1301
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1526
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1652
  · exact hroot.hOcc 1660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
