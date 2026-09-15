import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0266Refs : Fin 44 → RowRef 1665 43 := ![.occ 84, .occ 120, .occ 125, .occ 127, .occ 128, .occ 137, .occ 139, .occ 393, .occ 760, .occ 933, .occ 1100, .occ 1154, .occ 1160, .occ 1172, .occ 1186, .occ 1187, .occ 1220, .occ 1358, .occ 1470, .occ 1472, .occ 1477, .occ 1481, .occ 1488, .occ 1491, .occ 1567, .occ 1575, .occ 1641, .occ 1655, .sumGe, .nonneg 11, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchLe 13 (0), .branchLe 37 (0), .branchLe 10 (0), .branchLe 25 (0), .branchLe 35 (0), .branchGe 33 (1), .branchGe 41 (1)]

def plane484GenLeaf0266Mult : Fin 44 → Nat := ![3214, 6185, 2564, 304, 3150, 985, 6361, 4483, 428, 1762, 609, 25, 5092, 2262, 5446, 4298, 3357, 484, 450, 1741, 6892, 1464, 2406, 7822, 9179, 2130, 3128, 2280, 21203, 2155, 15461, 18219, 17162, 17938, 13857, 17325, 6813, 15813, 21178, 6010, 5843, 7143, 25741, 15301]

theorem plane484GenLeaf0266 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0266Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0266Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0266Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0266Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 120
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 393
  · exact hroot.hOcc 760
  · exact hroot.hOcc 933
  · exact hroot.hOcc 1100
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1575
  · exact hroot.hOcc 1641
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41

end QiushiMatmul
