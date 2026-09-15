import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0103Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 127, .occ 130, .occ 139, .occ 140, .occ 141, .occ 142, .occ 229, .occ 247, .occ 282, .occ 312, .occ 615, .occ 747, .occ 900, .occ 963, .occ 992, .occ 1058, .occ 1120, .occ 1143, .occ 1145, .occ 1147, .occ 1242, .occ 1254, .occ 1376, .occ 1384, .occ 1428, .occ 1442, .occ 1444, .occ 1478, .occ 1518, .occ 1602, .occ 1606, .occ 1630, .occ 1636, .sumGe, .nonneg 2, .branchLe 15 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchGe 26 (1), .branchGe 37 (1), .branchGe 34 (1), .branchLe 30 (0)]

def plane484GenLeaf0103Mult : Fin 44 → Nat := ![2263, 3185, 2318, 3766, 426, 162, 3737, 526, 979, 5976, 147, 124, 1426, 3064, 3478, 2450, 684, 1259, 941, 2942, 3662, 1810, 1178, 899, 461, 450, 808, 1280, 1316, 1360, 44, 494, 449, 831, 9142, 493, 2720, 8311, 26641, 9142, 21345, 22144, 7123, 9142]

theorem plane484GenLeaf0103 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0103Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0103Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0103Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0103Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 229
  · exact hroot.hOcc 247
  · exact hroot.hOcc 282
  · exact hroot.hOcc 312
  · exact hroot.hOcc 615
  · exact hroot.hOcc 747
  · exact hroot.hOcc 900
  · exact hroot.hOcc 963
  · exact hroot.hOcc 992
  · exact hroot.hOcc 1058
  · exact hroot.hOcc 1120
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1242
  · exact hroot.hOcc 1254
  · exact hroot.hOcc 1376
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1444
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1518
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1636
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30

end QiushiMatmul
