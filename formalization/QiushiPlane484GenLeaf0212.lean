import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0212Refs : Fin 39 → RowRef 1665 43 := ![.occ 121, .occ 132, .occ 134, .occ 139, .occ 141, .occ 216, .occ 248, .occ 259, .occ 316, .occ 326, .occ 383, .occ 520, .occ 572, .occ 638, .occ 677, .occ 734, .occ 1140, .occ 1160, .occ 1179, .occ 1233, .occ 1234, .occ 1306, .occ 1319, .occ 1391, .occ 1471, .occ 1499, .occ 1507, .occ 1516, .occ 1551, .occ 1623, .occ 1649, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchGe 18 (1), .branchGe 38 (1)]

def plane484GenLeaf0212Mult : Fin 39 → Nat := ![31, 33, 1, 24, 61, 26, 91, 71, 79, 71, 142, 60, 26, 17, 85, 108, 34, 30, 34, 25, 9, 31, 6, 18, 48, 82, 22, 59, 8, 50, 2, 174, 174, 174, 804, 642, 99, 818, 309]

theorem plane484GenLeaf0212 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0212Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0212Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0212Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0212Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 216
  · exact hroot.hOcc 248
  · exact hroot.hOcc 259
  · exact hroot.hOcc 316
  · exact hroot.hOcc 326
  · exact hroot.hOcc 383
  · exact hroot.hOcc 520
  · exact hroot.hOcc 572
  · exact hroot.hOcc 638
  · exact hroot.hOcc 677
  · exact hroot.hOcc 734
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1306
  · exact hroot.hOcc 1319
  · exact hroot.hOcc 1391
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1499
  · exact hroot.hOcc 1507
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1551
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1649
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
