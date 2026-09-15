import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0183Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 127, .occ 129, .occ 212, .occ 213, .occ 259, .occ 279, .occ 470, .occ 552, .occ 572, .occ 603, .occ 899, .occ 1119, .occ 1179, .occ 1214, .occ 1216, .occ 1227, .occ 1238, .occ 1239, .occ 1260, .occ 1273, .occ 1328, .occ 1357, .occ 1398, .occ 1488, .occ 1492, .occ 1546, .occ 1547, .occ 1606, .occ 1607, .occ 1634, .sumGe, .nonneg 2, .branchLe 15 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchLe 1 (0), .branchLe 5 (0), .branchGe 7 (1), .branchLe 39 (0), .branchLe 22 (0), .branchLe 19 (0)]

def plane484GenLeaf0183Mult : Fin 44 → Nat := ![2752, 623, 961, 1111, 1637, 3169, 1772, 1929, 206, 1353, 307, 396, 1348, 396, 1402, 396, 985, 198, 198, 1029, 1487, 656, 1002, 10, 2410, 1083, 198, 715, 1012, 305, 1608, 6428, 21, 6428, 11123, 14464, 4164, 6428, 4007, 3090, 12683, 6032, 5772, 6428]

theorem plane484GenLeaf0183 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0183Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0183Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0183Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0183Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 212
  · exact hroot.hOcc 213
  · exact hroot.hOcc 259
  · exact hroot.hOcc 279
  · exact hroot.hOcc 470
  · exact hroot.hOcc 552
  · exact hroot.hOcc 572
  · exact hroot.hOcc 603
  · exact hroot.hOcc 899
  · exact hroot.hOcc 1119
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1227
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1239
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1328
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1634
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19

end QiushiMatmul
