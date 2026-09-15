import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0093Refs : Fin 41 → RowRef 1665 43 := ![.occ 119, .occ 124, .occ 130, .occ 132, .occ 134, .occ 135, .occ 179, .occ 330, .occ 443, .occ 505, .occ 1059, .occ 1089, .occ 1143, .occ 1145, .occ 1235, .occ 1237, .occ 1240, .occ 1246, .occ 1253, .occ 1291, .occ 1292, .occ 1300, .occ 1412, .occ 1442, .occ 1478, .occ 1531, .occ 1540, .occ 1606, .occ 1635, .occ 1641, .occ 1663, .sumGe, .nonneg 0, .nonneg 12, .branchLe 15 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchLe 26 (0), .branchGe 24 (1), .branchGe 7 (1)]

def plane484GenLeaf0093Mult : Fin 41 → Nat := ![136, 48, 24, 71, 8, 8, 166, 1, 24, 16, 87, 22, 19, 76, 32, 8, 24, 24, 32, 49, 49, 27, 8, 8, 24, 8, 4, 8, 25, 22, 38, 198, 80, 508, 64, 144, 746, 198, 198, 364, 564]

theorem plane484GenLeaf0093 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0093Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0093Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0093Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0093Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 124
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 179
  · exact hroot.hOcc 330
  · exact hroot.hOcc 443
  · exact hroot.hOcc 505
  · exact hroot.hOcc 1059
  · exact hroot.hOcc 1089
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1235
  · exact hroot.hOcc 1237
  · exact hroot.hOcc 1240
  · exact hroot.hOcc 1246
  · exact hroot.hOcc 1253
  · exact hroot.hOcc 1291
  · exact hroot.hOcc 1292
  · exact hroot.hOcc 1300
  · exact hroot.hOcc 1412
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1531
  · exact hroot.hOcc 1540
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1635
  · exact hroot.hOcc 1641
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
