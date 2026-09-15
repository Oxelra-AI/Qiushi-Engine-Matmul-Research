import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0128Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 132, .occ 136, .occ 348, .occ 694, .occ 703, .occ 707, .occ 846, .occ 904, .occ 983, .occ 985, .occ 1100, .occ 1154, .occ 1215, .occ 1239, .occ 1248, .occ 1251, .occ 1285, .occ 1290, .occ 1321, .occ 1325, .occ 1491, .occ 1501, .occ 1517, .occ 1619, .occ 1622, .occ 1624, .occ 1630, .occ 1651, .occ 1653, .occ 1656, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchLe 32 (0), .branchGe 28 (1), .branchGe 6 (1), .branchLe 33 (0), .branchLe 42 (0)]

def plane484GenLeaf0128Mult : Fin 44 → Nat := ![9700, 12642, 9480, 3448, 17342, 7686, 7514, 8192, 314, 6440, 12364, 2534, 8134, 15306, 5950, 1614, 3804, 7222, 970, 5480, 9244, 7686, 148, 3096, 5502, 8325, 16003, 2332, 652, 448, 14497, 12671, 62166, 36738, 58570, 55928, 59834, 11900, 30224, 61718, 30942, 51864, 53590, 61366]

theorem plane484GenLeaf0128 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0128Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0128Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0128Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0128Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 348
  · exact hroot.hOcc 694
  · exact hroot.hOcc 703
  · exact hroot.hOcc 707
  · exact hroot.hOcc 846
  · exact hroot.hOcc 904
  · exact hroot.hOcc 983
  · exact hroot.hOcc 985
  · exact hroot.hOcc 1100
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1239
  · exact hroot.hOcc 1248
  · exact hroot.hOcc 1251
  · exact hroot.hOcc 1285
  · exact hroot.hOcc 1290
  · exact hroot.hOcc 1321
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1501
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1651
  · exact hroot.hOcc 1653
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42

end QiushiMatmul
