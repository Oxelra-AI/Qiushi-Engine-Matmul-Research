import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0373Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 123, .occ 124, .occ 131, .occ 132, .occ 133, .occ 136, .occ 138, .occ 180, .occ 225, .occ 237, .occ 331, .occ 523, .occ 549, .occ 1119, .occ 1124, .occ 1144, .occ 1146, .occ 1173, .occ 1213, .occ 1353, .occ 1481, .occ 1496, .occ 1527, .occ 1567, .occ 1573, .occ 1606, .occ 1640, .occ 1649, .sumGe, .nonneg 15, .nonneg 16, .nonneg 21, .nonneg 26, .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchLe 30 (0), .branchLe 42 (0), .branchLe 27 (0), .branchLe 9 (0), .branchLe 34 (0), .branchGe 28 (1)]

def plane484GenLeaf0373Mult : Fin 44 → Nat := ![70, 263, 426, 970, 630, 720, 35, 521, 78, 332, 103, 589, 276, 685, 32, 600, 181, 1313, 67, 256, 323, 635, 148, 140, 45, 397, 186, 425, 670, 2246, 530, 290, 240, 314, 2253, 1718, 4714, 2916, 1782, 1277, 933, 1294, 1667, 3125]

theorem plane484GenLeaf0373 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0373Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0373Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0373Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0373Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 180
  · exact hroot.hOcc 225
  · exact hroot.hOcc 237
  · exact hroot.hOcc 331
  · exact hroot.hOcc 523
  · exact hroot.hOcc 549
  · exact hroot.hOcc 1119
  · exact hroot.hOcc 1124
  · exact hroot.hOcc 1144
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1527
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1640
  · exact hroot.hOcc 1649
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
