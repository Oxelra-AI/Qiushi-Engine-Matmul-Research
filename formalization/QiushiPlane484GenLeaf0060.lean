import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0060Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 122, .occ 123, .occ 126, .occ 129, .occ 139, .occ 237, .occ 327, .occ 628, .occ 913, .occ 936, .occ 1148, .occ 1172, .occ 1191, .occ 1213, .occ 1226, .occ 1247, .occ 1260, .occ 1263, .occ 1281, .occ 1282, .occ 1325, .occ 1400, .occ 1459, .occ 1504, .occ 1508, .occ 1531, .occ 1580, .occ 1624, .occ 1644, .occ 1657, .occ 1658, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchLe 42 (0), .branchLe 0 (0), .branchLe 10 (0), .branchLe 20 (0), .branchGe 36 (1), .branchGe 32 (1)]

def plane484GenLeaf0060Mult : Fin 44 → Nat := ![942, 2001, 6233, 766, 357, 90, 2664, 147, 1264, 1029, 806, 2254, 5477, 4474, 180, 6463, 8711, 10560, 5024, 1855, 3824, 2063, 1237, 2673, 766, 2195, 1930, 13869, 3196, 7605, 6562, 4556, 33127, 28571, 14049, 33127, 22415, 34636, 29217, 24097, 23444, 26565, 33250, 34737]

theorem plane484GenLeaf0060 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0060Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0060Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0060Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0060Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 129
  · exact hroot.hOcc 139
  · exact hroot.hOcc 237
  · exact hroot.hOcc 327
  · exact hroot.hOcc 628
  · exact hroot.hOcc 913
  · exact hroot.hOcc 936
  · exact hroot.hOcc 1148
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1226
  · exact hroot.hOcc 1247
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1263
  · exact hroot.hOcc 1281
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1400
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1504
  · exact hroot.hOcc 1508
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1657
  · exact hroot.hOcc 1658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32

end QiushiMatmul
