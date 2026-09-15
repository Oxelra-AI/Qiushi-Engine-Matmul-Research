import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0066Refs : Fin 43 → RowRef 1665 43 := ![.occ 105, .occ 121, .occ 122, .occ 129, .occ 130, .occ 132, .occ 134, .occ 139, .occ 141, .occ 142, .occ 318, .occ 548, .occ 602, .occ 630, .occ 1158, .occ 1170, .occ 1190, .occ 1191, .occ 1196, .occ 1206, .occ 1213, .occ 1220, .occ 1316, .occ 1437, .occ 1458, .occ 1533, .occ 1602, .occ 1645, .occ 1650, .occ 1657, .sumGe, .nonneg 5, .nonneg 14, .nonneg 23, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchLe 42 (0), .branchGe 0 (1), .branchLe 32 (0), .branchLe 26 (0)]

def plane484GenLeaf0066Mult : Fin 43 → Nat := ![34, 60, 20, 255, 206, 196, 27, 15, 10, 39, 8, 6, 50, 30, 28, 35, 54, 59, 11, 28, 80, 115, 64, 42, 64, 8, 132, 4, 40, 13, 347, 17, 326, 33, 248, 219, 347, 39, 760, 109, 669, 312, 243]

theorem plane484GenLeaf0066 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0066Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0066Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0066Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0066Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 318
  · exact hroot.hOcc 548
  · exact hroot.hOcc 602
  · exact hroot.hOcc 630
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1316
  · exact hroot.hOcc 1437
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1533
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1645
  · exact hroot.hOcc 1650
  · exact hroot.hOcc 1657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26

end QiushiMatmul
