import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0108Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 127, .occ 132, .occ 203, .occ 209, .occ 282, .occ 341, .occ 357, .occ 399, .occ 480, .occ 811, .occ 861, .occ 1136, .occ 1143, .occ 1168, .occ 1208, .occ 1213, .occ 1231, .occ 1239, .occ 1245, .occ 1278, .occ 1282, .occ 1322, .occ 1325, .occ 1346, .occ 1437, .occ 1455, .occ 1476, .occ 1573, .occ 1615, .occ 1624, .occ 1661, .occ 1663, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchGe 36 (1), .branchLe 26 (0), .branchLe 19 (0), .branchGe 34 (1), .branchLe 20 (0)]

def plane484GenLeaf0108Mult : Fin 43 → Nat := ![1366, 2274, 1006, 2554, 3026, 1882, 800, 488, 1570, 1704, 164, 1218, 506, 712, 88, 206, 294, 596, 98, 196, 183, 116, 614, 85, 70, 1347, 1319, 252, 792, 254, 116, 879, 29, 4244, 3990, 2740, 3738, 13358, 11838, 3364, 4048, 8196, 4244]

theorem plane484GenLeaf0108 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0108Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0108Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0108Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0108Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 127
  · exact hroot.hOcc 132
  · exact hroot.hOcc 203
  · exact hroot.hOcc 209
  · exact hroot.hOcc 282
  · exact hroot.hOcc 341
  · exact hroot.hOcc 357
  · exact hroot.hOcc 399
  · exact hroot.hOcc 480
  · exact hroot.hOcc 811
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1231
  · exact hroot.hOcc 1239
  · exact hroot.hOcc 1245
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1322
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1346
  · exact hroot.hOcc 1437
  · exact hroot.hOcc 1455
  · exact hroot.hOcc 1476
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1661
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20

end QiushiMatmul
