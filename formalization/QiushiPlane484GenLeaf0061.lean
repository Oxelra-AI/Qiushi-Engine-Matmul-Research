import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0061Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 129, .occ 134, .occ 137, .occ 140, .occ 141, .occ 315, .occ 459, .occ 492, .occ 534, .occ 661, .occ 1027, .occ 1170, .occ 1173, .occ 1242, .occ 1244, .occ 1272, .occ 1277, .occ 1406, .occ 1414, .occ 1458, .occ 1522, .occ 1524, .occ 1579, .occ 1580, .occ 1602, .occ 1617, .occ 1624, .occ 1627, .occ 1645, .occ 1650, .occ 1657, .sumGe, .nonneg 0, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchLe 42 (0), .branchLe 10 (0), .branchGe 20 (1), .branchLe 40 (0)]

def plane484GenLeaf0061Mult : Fin 44 → Nat := ![5650, 15, 26284, 28315, 20820, 11317, 2329, 235, 7020, 21656, 4624, 3383, 12731, 33319, 3036, 168, 3023, 1094, 192, 100, 10712, 1145, 16, 1370, 189, 1694, 31300, 192, 3207, 18246, 32500, 1137, 597, 68101, 31566, 5678, 14577, 68101, 63581, 85668, 6598, 66964, 166928, 64468]

theorem plane484GenLeaf0061 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0061Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0061Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0061Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0061Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 315
  · exact hroot.hOcc 459
  · exact hroot.hOcc 492
  · exact hroot.hOcc 534
  · exact hroot.hOcc 661
  · exact hroot.hOcc 1027
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1242
  · exact hroot.hOcc 1244
  · exact hroot.hOcc 1272
  · exact hroot.hOcc 1277
  · exact hroot.hOcc 1406
  · exact hroot.hOcc 1414
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1579
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1617
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1627
  · exact hroot.hOcc 1645
  · exact hroot.hOcc 1650
  · exact hroot.hOcc 1657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40

end QiushiMatmul
