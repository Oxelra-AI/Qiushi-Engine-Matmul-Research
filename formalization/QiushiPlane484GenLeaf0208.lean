import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0208Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 123, .occ 128, .occ 132, .occ 140, .occ 141, .occ 142, .occ 196, .occ 328, .occ 368, .occ 431, .occ 1096, .occ 1140, .occ 1160, .occ 1166, .occ 1179, .occ 1216, .occ 1303, .occ 1308, .occ 1427, .occ 1430, .occ 1472, .occ 1478, .occ 1597, .occ 1601, .occ 1607, .occ 1644, .occ 1649, .sumGe, .nonneg 4, .nonneg 5, .nonneg 7, .nonneg 12, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchGe 1 (1), .branchGe 22 (1), .branchGe 0 (1), .branchGe 8 (1), .branchGe 3 (1)]

def plane484GenLeaf0208Mult : Fin 44 → Nat := ![945, 652, 893, 317, 211, 226, 128, 468, 128, 492, 476, 164, 296, 24, 340, 56, 52, 232, 29, 61, 232, 344, 188, 184, 24, 124, 105, 28, 973, 212, 744, 436, 2232, 402, 216, 996, 1176, 548, 146, 1227, 2024, 1207, 2668, 4132]

theorem plane484GenLeaf0208 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0208Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0208Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0208Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0208Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 196
  · exact hroot.hOcc 328
  · exact hroot.hOcc 368
  · exact hroot.hOcc 431
  · exact hroot.hOcc 1096
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1308
  · exact hroot.hOcc 1427
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1649
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
