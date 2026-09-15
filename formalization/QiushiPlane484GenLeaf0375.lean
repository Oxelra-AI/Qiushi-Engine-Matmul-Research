import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0375Refs : Fin 42 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 125, .occ 127, .occ 130, .occ 131, .occ 132, .occ 133, .occ 134, .occ 137, .occ 138, .occ 221, .occ 690, .occ 1115, .occ 1143, .occ 1151, .occ 1179, .occ 1186, .occ 1206, .occ 1216, .occ 1347, .occ 1357, .occ 1496, .occ 1505, .occ 1515, .occ 1516, .occ 1567, .occ 1606, .occ 1619, .occ 1640, .sumGe, .nonneg 8, .nonneg 21, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchLe 30 (0), .branchLe 42 (0), .branchLe 27 (0), .branchGe 9 (1)]

def plane484GenLeaf0375Mult : Fin 42 → Nat := ![110, 1250, 620, 372, 98, 55, 145, 454, 470, 723, 369, 880, 828, 44, 56, 56, 56, 568, 200, 526, 98, 464, 100, 40, 166, 412, 156, 170, 216, 156, 1718, 1076, 268, 268, 2280, 1236, 2680, 1024, 1038, 1448, 1718, 5300]

theorem plane484GenLeaf0375 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0375Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0375Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0375Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0375Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 221
  · exact hroot.hOcc 690
  · exact hroot.hOcc 1115
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1347
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1515
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1640
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
