import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0065Refs : Fin 43 → RowRef 1665 43 := ![.occ 122, .occ 124, .occ 130, .occ 225, .occ 290, .occ 590, .occ 604, .occ 998, .occ 1002, .occ 1078, .occ 1183, .occ 1187, .occ 1190, .occ 1196, .occ 1225, .occ 1226, .occ 1233, .occ 1250, .occ 1254, .occ 1298, .occ 1319, .occ 1346, .occ 1441, .occ 1530, .occ 1539, .occ 1552, .occ 1580, .occ 1626, .occ 1635, .occ 1650, .occ 1655, .sumGe, .nonneg 1, .nonneg 3, .nonneg 4, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 13 (1), .branchLe 42 (0), .branchLe 0 (0), .branchGe 10 (1), .branchGe 28 (1)]

def plane484GenLeaf0065Mult : Fin 43 → Nat := ![24453, 15546, 13024, 3209, 2010, 1801, 14601, 3182, 10672, 8884, 1603, 589, 2001, 7800, 230, 8039, 3613, 5637, 8675, 7194, 3966, 1627, 3159, 3966, 8359, 6208, 3592, 2986, 302, 1395, 4407, 30844, 3003, 8643, 79638, 17783, 3003, 30844, 114068, 27383, 12824, 113275, 81307]

theorem plane484GenLeaf0065 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0065Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0065Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0065Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0065Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 130
  · exact hroot.hOcc 225
  · exact hroot.hOcc 290
  · exact hroot.hOcc 590
  · exact hroot.hOcc 604
  · exact hroot.hOcc 998
  · exact hroot.hOcc 1002
  · exact hroot.hOcc 1078
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1225
  · exact hroot.hOcc 1226
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1250
  · exact hroot.hOcc 1254
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1319
  · exact hroot.hOcc 1346
  · exact hroot.hOcc 1441
  · exact hroot.hOcc 1530
  · exact hroot.hOcc 1539
  · exact hroot.hOcc 1552
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1635
  · exact hroot.hOcc 1650
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
