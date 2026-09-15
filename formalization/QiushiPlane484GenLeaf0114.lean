import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0114Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 122, .occ 130, .occ 140, .occ 209, .occ 387, .occ 558, .occ 652, .occ 707, .occ 855, .occ 856, .occ 891, .occ 912, .occ 918, .occ 990, .occ 1123, .occ 1130, .occ 1143, .occ 1146, .occ 1147, .occ 1342, .occ 1347, .occ 1368, .occ 1388, .occ 1456, .occ 1472, .occ 1496, .occ 1540, .occ 1553, .occ 1615, .occ 1618, .occ 1654, .sumGe, .nonneg 10, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchGe 36 (1), .branchGe 26 (1), .branchLe 21 (0), .branchLe 18 (0), .branchGe 35 (1)]

def plane484GenLeaf0114Mult : Fin 43 → Nat := ![83, 712, 478, 410, 970, 964, 52, 1782, 686, 1845, 465, 764, 810, 130, 625, 611, 397, 22, 344, 178, 87, 84, 223, 220, 55, 112, 1421, 582, 52, 138, 387, 324, 2169, 52, 487, 204, 748, 10432, 1442, 9159, 1970, 966, 8812]

theorem plane484GenLeaf0114 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0114Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0114Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0114Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0114Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 122
  · exact hroot.hOcc 130
  · exact hroot.hOcc 140
  · exact hroot.hOcc 209
  · exact hroot.hOcc 387
  · exact hroot.hOcc 558
  · exact hroot.hOcc 652
  · exact hroot.hOcc 707
  · exact hroot.hOcc 855
  · exact hroot.hOcc 856
  · exact hroot.hOcc 891
  · exact hroot.hOcc 912
  · exact hroot.hOcc 918
  · exact hroot.hOcc 990
  · exact hroot.hOcc 1123
  · exact hroot.hOcc 1130
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1347
  · exact hroot.hOcc 1368
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1456
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1540
  · exact hroot.hOcc 1553
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1654
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
