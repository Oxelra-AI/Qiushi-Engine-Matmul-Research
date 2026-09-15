import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0226Refs : Fin 43 → RowRef 1665 43 := ![.occ 103, .occ 123, .occ 125, .occ 126, .occ 132, .occ 134, .occ 135, .occ 136, .occ 138, .occ 208, .occ 210, .occ 533, .occ 1094, .occ 1140, .occ 1143, .occ 1145, .occ 1146, .occ 1147, .occ 1170, .occ 1172, .occ 1173, .occ 1319, .occ 1348, .occ 1353, .occ 1477, .occ 1580, .occ 1597, .occ 1644, .occ 1654, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchLe 16 (0), .branchLe 31 (0), .branchGe 22 (1), .branchLe 8 (0), .branchLe 42 (0), .branchLe 10 (0)]

def plane484GenLeaf0226Mult : Fin 43 → Nat := ![200, 2459, 2181, 422, 682, 2356, 89, 2146, 2627, 1000, 870, 1182, 26, 2273, 819, 1170, 248, 371, 452, 696, 2981, 418, 574, 2569, 1288, 178, 363, 800, 922, 7380, 3742, 5952, 6036, 1070, 2616, 2538, 2830, 1504, 7380, 13856, 1940, 6092, 6958]

theorem plane484GenLeaf0226 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0226Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0226Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0226Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0226Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 103
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 208
  · exact hroot.hOcc 210
  · exact hroot.hOcc 533
  · exact hroot.hOcc 1094
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1319
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1654
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
