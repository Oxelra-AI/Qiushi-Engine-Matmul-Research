import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0007Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 120, .occ 127, .occ 128, .occ 133, .occ 134, .occ 258, .occ 451, .occ 554, .occ 764, .occ 1174, .occ 1187, .occ 1193, .occ 1196, .occ 1226, .occ 1267, .occ 1270, .occ 1325, .occ 1369, .occ 1371, .occ 1422, .occ 1458, .occ 1489, .occ 1553, .occ 1606, .occ 1621, .occ 1628, .occ 1644, .occ 1645, .occ 1647, .occ 1661, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchLe 41 (0), .branchGe 8 (1), .branchGe 9 (1), .branchLe 40 (0), .branchLe 26 (0)]

def plane484GenLeaf0007Mult : Fin 44 → Nat := ![42417, 67549, 30142, 21904, 12806, 64584, 13192, 8985, 1986, 13779, 23838, 61733, 4369, 2874, 12130, 6558, 8479, 18010, 5464, 15067, 22457, 10318, 66154, 26013, 16300, 38571, 15298, 10171, 6707, 7740, 14053, 178890, 105739, 19142, 178890, 92278, 71642, 108107, 152419, 117157, 86328, 209872, 104996, 163592]

theorem plane484GenLeaf0007 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0007Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0007Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 258
  · exact hroot.hOcc 451
  · exact hroot.hOcc 554
  · exact hroot.hOcc 764
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1193
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1226
  · exact hroot.hOcc 1267
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1369
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1553
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1621
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1645
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26

end QiushiMatmul
