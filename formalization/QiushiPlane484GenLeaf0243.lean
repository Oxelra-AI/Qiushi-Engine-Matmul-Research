import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0243Refs : Fin 44 → RowRef 1665 43 := ![.occ 105, .occ 124, .occ 125, .occ 130, .occ 135, .occ 198, .occ 268, .occ 335, .occ 354, .occ 431, .occ 809, .occ 1137, .occ 1143, .occ 1145, .occ 1150, .occ 1154, .occ 1183, .occ 1187, .occ 1200, .occ 1220, .occ 1288, .occ 1292, .occ 1333, .occ 1430, .occ 1451, .occ 1477, .occ 1478, .occ 1489, .occ 1602, .occ 1618, .occ 1647, .sumGe, .nonneg 21, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchLe 16 (0), .branchGe 31 (1), .branchGe 20 (1), .branchGe 4 (1)]

def plane484GenLeaf0243Mult : Fin 44 → Nat := ![12, 963, 804, 978, 1388, 1359, 312, 24, 7, 184, 151, 46, 257, 21, 699, 198, 215, 192, 72, 427, 313, 16, 111, 236, 50, 1252, 94, 158, 302, 490, 87, 2243, 267, 343, 1914, 472, 2007, 1753, 2045, 1666, 2156, 1304, 4150, 5569]

theorem plane484GenLeaf0243 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0243Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0243Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0243Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0243Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 198
  · exact hroot.hOcc 268
  · exact hroot.hOcc 335
  · exact hroot.hOcc 354
  · exact hroot.hOcc 431
  · exact hroot.hOcc 809
  · exact hroot.hOcc 1137
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1288
  · exact hroot.hOcc 1292
  · exact hroot.hOcc 1333
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1451
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1647
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
