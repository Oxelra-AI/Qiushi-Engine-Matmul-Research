import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0386Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 125, .occ 137, .occ 277, .occ 326, .occ 600, .occ 615, .occ 627, .occ 709, .occ 710, .occ 711, .occ 754, .occ 1191, .occ 1220, .occ 1224, .occ 1252, .occ 1274, .occ 1383, .occ 1389, .occ 1422, .occ 1425, .occ 1426, .occ 1481, .occ 1483, .occ 1486, .occ 1492, .occ 1571, .occ 1573, .occ 1606, .occ 1624, .occ 1637, .occ 1638, .occ 1661, .sumGe, .nonneg 20, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchGe 30 (1), .branchGe 42 (1), .branchLe 39 (0), .branchLe 1 (0)]

def plane484GenLeaf0386Mult : Fin 44 → Nat := ![343, 281, 543, 66, 421, 131, 99, 55, 104, 442, 203, 100, 7, 462, 33, 177, 22, 7, 23, 17, 81, 84, 16, 100, 191, 385, 206, 376, 187, 195, 49, 60, 25, 968, 298, 819, 1589, 354, 1242, 2633, 1807, 1106, 843, 968]

theorem plane484GenLeaf0386 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0386Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0386Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0386Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0386Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 137
  · exact hroot.hOcc 277
  · exact hroot.hOcc 326
  · exact hroot.hOcc 600
  · exact hroot.hOcc 615
  · exact hroot.hOcc 627
  · exact hroot.hOcc 709
  · exact hroot.hOcc 710
  · exact hroot.hOcc 711
  · exact hroot.hOcc 754
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1224
  · exact hroot.hOcc 1252
  · exact hroot.hOcc 1274
  · exact hroot.hOcc 1383
  · exact hroot.hOcc 1389
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1425
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1637
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1

end QiushiMatmul
