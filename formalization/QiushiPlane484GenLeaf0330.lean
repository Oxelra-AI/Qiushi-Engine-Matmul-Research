import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0330Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 121, .occ 122, .occ 123, .occ 125, .occ 128, .occ 134, .occ 137, .occ 139, .occ 140, .occ 289, .occ 325, .occ 338, .occ 366, .occ 827, .occ 855, .occ 1140, .occ 1150, .occ 1215, .occ 1216, .occ 1448, .occ 1457, .occ 1478, .occ 1488, .occ 1495, .occ 1551, .occ 1573, .occ 1600, .occ 1604, .occ 1607, .occ 1659, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchGe 26 (1), .branchLe 14 (0), .branchGe 1 (1), .branchGe 30 (1), .branchLe 36 (0), .branchLe 27 (0), .branchLe 37 (0), .branchLe 17 (0)]

def plane484GenLeaf0330Mult : Fin 44 → Nat := ![416, 356, 554, 338, 10, 274, 103, 604, 1211, 285, 48, 590, 588, 13, 820, 240, 472, 268, 908, 700, 148, 165, 468, 148, 200, 176, 668, 159, 76, 880, 160, 2404, 1356, 202, 972, 274, 5674, 1944, 2660, 1828, 1036, 2244, 1664, 1356]

theorem plane484GenLeaf0330 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0330Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0330Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0330Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0330Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 289
  · exact hroot.hOcc 325
  · exact hroot.hOcc 338
  · exact hroot.hOcc 366
  · exact hroot.hOcc 827
  · exact hroot.hOcc 855
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1448
  · exact hroot.hOcc 1457
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1495
  · exact hroot.hOcc 1551
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1600
  · exact hroot.hOcc 1604
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17

end QiushiMatmul
