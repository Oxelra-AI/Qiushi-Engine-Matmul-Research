import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0272Refs : Fin 44 → RowRef 1665 43 := ![.occ 105, .occ 126, .occ 135, .occ 283, .occ 311, .occ 470, .occ 486, .occ 1124, .occ 1132, .occ 1146, .occ 1151, .occ 1154, .occ 1159, .occ 1180, .occ 1211, .occ 1220, .occ 1279, .occ 1313, .occ 1411, .occ 1471, .occ 1472, .occ 1523, .occ 1567, .occ 1571, .occ 1603, .occ 1609, .occ 1610, .occ 1648, .occ 1653, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchLe 13 (0), .branchGe 37 (1), .branchLe 32 (0), .branchLe 8 (0), .branchLe 9 (0), .branchLe 30 (0), .branchLe 4 (0)]

def plane484GenLeaf0272Mult : Fin 44 → Nat := ![3847, 2837, 4546, 3985, 285, 996, 1856, 431, 1244, 368, 637, 1732, 1703, 5150, 556, 2340, 1544, 1710, 109, 2652, 2526, 117, 1661, 430, 5207, 978, 3230, 1113, 2183, 14702, 4552, 1403, 8030, 10505, 14334, 7758, 12569, 14702, 11264, 10313, 7517, 12519, 10630, 11882]

theorem plane484GenLeaf0272 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0272Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0272Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0272Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0272Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 126
  · exact hroot.hOcc 135
  · exact hroot.hOcc 283
  · exact hroot.hOcc 311
  · exact hroot.hOcc 470
  · exact hroot.hOcc 486
  · exact hroot.hOcc 1124
  · exact hroot.hOcc 1132
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1180
  · exact hroot.hOcc 1211
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1279
  · exact hroot.hOcc 1313
  · exact hroot.hOcc 1411
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1523
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1648
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
