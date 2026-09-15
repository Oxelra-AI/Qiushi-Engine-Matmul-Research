import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0105Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 125, .occ 127, .occ 128, .occ 202, .occ 208, .occ 282, .occ 341, .occ 354, .occ 653, .occ 861, .occ 1140, .occ 1158, .occ 1223, .occ 1234, .occ 1238, .occ 1239, .occ 1252, .occ 1261, .occ 1347, .occ 1348, .occ 1388, .occ 1437, .occ 1470, .occ 1472, .occ 1477, .occ 1573, .occ 1580, .occ 1615, .occ 1638, .occ 1657, .occ 1661, .occ 1663, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchGe 36 (1), .branchLe 26 (0), .branchLe 19 (0), .branchLe 34 (0), .branchLe 25 (0)]

def plane484GenLeaf0105Mult : Fin 43 → Nat := ![2384, 236, 4535, 203, 439, 3958, 6276, 3205, 2266, 6573, 3620, 140, 3606, 353, 353, 461, 1880, 1836, 1905, 1842, 155, 92, 2335, 353, 1648, 539, 102, 353, 579, 1023, 909, 3600, 2131, 12300, 8115, 10939, 12160, 35239, 25228, 11384, 7477, 11761, 10368]

theorem plane484GenLeaf0105 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0105Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0105Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0105Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0105Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 202
  · exact hroot.hOcc 208
  · exact hroot.hOcc 282
  · exact hroot.hOcc 341
  · exact hroot.hOcc 354
  · exact hroot.hOcc 653
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1223
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1239
  · exact hroot.hOcc 1252
  · exact hroot.hOcc 1261
  · exact hroot.hOcc 1347
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1437
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1657
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
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25

end QiushiMatmul
