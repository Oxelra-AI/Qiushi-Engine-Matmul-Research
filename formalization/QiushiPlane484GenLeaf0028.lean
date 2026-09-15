import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0028Refs : Fin 44 → RowRef 1665 43 := ![.occ 139, .occ 140, .occ 375, .occ 444, .occ 471, .occ 480, .occ 633, .occ 665, .occ 704, .occ 766, .occ 800, .occ 804, .occ 1140, .occ 1166, .occ 1170, .occ 1221, .occ 1281, .occ 1327, .occ 1348, .occ 1378, .occ 1388, .occ 1429, .occ 1478, .occ 1603, .occ 1606, .occ 1608, .occ 1617, .occ 1627, .occ 1630, .occ 1659, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchLe 25 (0), .branchLe 18 (0), .branchGe 42 (1), .branchLe 23 (0), .branchLe 14 (0), .branchGe 24 (1)]

def plane484GenLeaf0028Mult : Fin 44 → Nat := ![1770, 565, 133, 1717, 908, 248, 335, 156, 889, 737, 1980, 288, 277, 456, 663, 1, 214, 1505, 576, 1107, 1020, 2544, 831, 772, 2750, 445, 333, 1356, 950, 330, 5749, 1108, 5749, 4244, 4585, 3286, 2878, 11786, 4641, 1435, 9361, 2543, 3779, 12985]

theorem plane484GenLeaf0028 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0028Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0028Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0028Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0028Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 375
  · exact hroot.hOcc 444
  · exact hroot.hOcc 471
  · exact hroot.hOcc 480
  · exact hroot.hOcc 633
  · exact hroot.hOcc 665
  · exact hroot.hOcc 704
  · exact hroot.hOcc 766
  · exact hroot.hOcc 800
  · exact hroot.hOcc 804
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1221
  · exact hroot.hOcc 1281
  · exact hroot.hOcc 1327
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1378
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1617
  · exact hroot.hOcc 1627
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
