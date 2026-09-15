import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0333Refs : Fin 41 → RowRef 1665 43 := ![.occ 84, .occ 139, .occ 140, .occ 141, .occ 142, .occ 386, .occ 757, .occ 808, .occ 827, .occ 836, .occ 855, .occ 859, .occ 1083, .occ 1140, .occ 1147, .occ 1150, .occ 1174, .occ 1214, .occ 1393, .occ 1443, .occ 1459, .occ 1496, .occ 1520, .occ 1573, .occ 1607, .occ 1659, .sumGe, .nonneg 3, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchGe 26 (1), .branchLe 14 (0), .branchGe 1 (1), .branchGe 30 (1), .branchLe 36 (0), .branchGe 27 (1), .branchLe 17 (0), .branchLe 38 (0), .branchLe 10 (0)]

def plane484GenLeaf0333Mult : Fin 41 → Nat := ![104, 321, 55, 175, 121, 38, 52, 56, 60, 80, 52, 272, 64, 148, 192, 52, 52, 172, 16, 132, 104, 40, 192, 152, 132, 16, 548, 64, 148, 146, 232, 22, 1570, 548, 356, 556, 356, 220, 148, 400, 532]

theorem plane484GenLeaf0333 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0333Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0333Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0333Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0333Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 386
  · exact hroot.hOcc 757
  · exact hroot.hOcc 808
  · exact hroot.hOcc 827
  · exact hroot.hOcc 836
  · exact hroot.hOcc 855
  · exact hroot.hOcc 859
  · exact hroot.hOcc 1083
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1393
  · exact hroot.hOcc 1443
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1520
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
