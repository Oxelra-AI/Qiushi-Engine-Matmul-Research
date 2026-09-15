import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0123Refs : Fin 44 → RowRef 1665 43 := ![.occ 92, .occ 132, .occ 137, .occ 240, .occ 457, .occ 606, .occ 631, .occ 860, .occ 1023, .occ 1078, .occ 1197, .occ 1215, .occ 1223, .occ 1224, .occ 1258, .occ 1290, .occ 1312, .occ 1352, .occ 1353, .occ 1517, .occ 1542, .occ 1603, .occ 1619, .occ 1620, .occ 1622, .occ 1625, .occ 1639, .occ 1642, .occ 1652, .occ 1656, .occ 1659, .sumGe, .nonneg 3, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchLe 32 (0), .branchGe 28 (1), .branchLe 6 (0), .branchLe 42 (0), .branchLe 1 (0)]

def plane484GenLeaf0123Mult : Fin 44 → Nat := ![7110, 8416, 2286, 2296, 776, 11626, 1742, 768, 8446, 4290, 886, 3250, 14292, 9174, 7938, 2392, 5856, 19786, 4122, 3356, 14086, 6200, 26418, 8220, 5977, 1597, 1573, 5619, 2292, 6658, 3940, 64890, 5728, 20644, 54526, 52518, 56670, 45356, 50940, 64890, 32882, 51084, 54750, 51922]

theorem plane484GenLeaf0123 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0123Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0123Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0123Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0123Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 92
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 240
  · exact hroot.hOcc 457
  · exact hroot.hOcc 606
  · exact hroot.hOcc 631
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1023
  · exact hroot.hOcc 1078
  · exact hroot.hOcc 1197
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1223
  · exact hroot.hOcc 1224
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1290
  · exact hroot.hOcc 1312
  · exact hroot.hOcc 1352
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1542
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1642
  · exact hroot.hOcc 1652
  · exact hroot.hOcc 1656
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1

end QiushiMatmul
