import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0073Refs : Fin 43 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 130, .occ 132, .occ 176, .occ 366, .occ 544, .occ 627, .occ 710, .occ 801, .occ 804, .occ 805, .occ 807, .occ 1096, .occ 1173, .occ 1190, .occ 1226, .occ 1260, .occ 1322, .occ 1398, .occ 1403, .occ 1414, .occ 1416, .occ 1419, .occ 1425, .occ 1430, .occ 1458, .occ 1472, .occ 1559, .occ 1607, .occ 1624, .occ 1644, .sumGe, .nonneg 9, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchGe 42 (1), .branchLe 20 (0), .branchLe 7 (0), .branchGe 3 (1)]

def plane484GenLeaf0073Mult : Fin 43 → Nat := ![2128, 2285, 1751, 373, 45, 188, 730, 88, 297, 1394, 84, 1611, 180, 630, 84, 45, 346, 199, 1483, 69, 30, 170, 1984, 73, 591, 69, 214, 99, 316, 30, 15, 42, 2441, 8767, 2253, 69, 1777, 690, 10187, 4454, 2202, 69, 12795]

theorem plane484GenLeaf0073 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0073Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0073Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0073Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0073Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 176
  · exact hroot.hOcc 366
  · exact hroot.hOcc 544
  · exact hroot.hOcc 627
  · exact hroot.hOcc 710
  · exact hroot.hOcc 801
  · exact hroot.hOcc 804
  · exact hroot.hOcc 805
  · exact hroot.hOcc 807
  · exact hroot.hOcc 1096
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1226
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1322
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1414
  · exact hroot.hOcc 1416
  · exact hroot.hOcc 1419
  · exact hroot.hOcc 1425
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1559
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1644
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
