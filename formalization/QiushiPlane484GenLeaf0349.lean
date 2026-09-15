import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0349Refs : Fin 44 → RowRef 1665 43 := ![.occ 125, .occ 129, .occ 130, .occ 136, .occ 137, .occ 138, .occ 139, .occ 284, .occ 631, .occ 816, .occ 818, .occ 1102, .occ 1168, .occ 1183, .occ 1188, .occ 1196, .occ 1213, .occ 1405, .occ 1423, .occ 1425, .occ 1462, .occ 1472, .occ 1477, .occ 1478, .occ 1481, .occ 1491, .occ 1538, .occ 1557, .occ 1580, .occ 1600, .occ 1607, .occ 1622, .sumGe, .nonneg 11, .nonneg 24, .branchLe 15 (0), .branchGe 2 (1), .branchLe 23 (0), .branchGe 26 (1), .branchGe 14 (1), .branchGe 36 (1), .branchGe 30 (1), .branchLe 12 (0), .branchLe 40 (0)]

def plane484GenLeaf0349Mult : Fin 44 → Nat := ![6521, 4494, 3928, 860, 4892, 2817, 2253, 6140, 4194, 920, 6747, 2347, 12, 2974, 2070, 896, 2930, 304, 740, 381, 1619, 12, 773, 56, 2641, 3053, 894, 1711, 4529, 2581, 12, 1145, 12172, 1407, 142, 6140, 16899, 1533, 22000, 38558, 8031, 22493, 3094, 12160]

theorem plane484GenLeaf0349 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0349Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0349Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0349Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0349Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 284
  · exact hroot.hOcc 631
  · exact hroot.hOcc 816
  · exact hroot.hOcc 818
  · exact hroot.hOcc 1102
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1423
  · exact hroot.hOcc 1425
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1600
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1622
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40

end QiushiMatmul
