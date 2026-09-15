import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0279Refs : Fin 43 → RowRef 1665 43 := ![.occ 125, .occ 128, .occ 129, .occ 135, .occ 136, .occ 216, .occ 230, .occ 234, .occ 403, .occ 572, .occ 784, .occ 1180, .occ 1186, .occ 1187, .occ 1200, .occ 1223, .occ 1302, .occ 1383, .occ 1471, .occ 1481, .occ 1491, .occ 1507, .occ 1524, .occ 1528, .occ 1567, .occ 1608, .sumGe, .nonneg 3, .nonneg 5, .nonneg 7, .nonneg 9, .nonneg 11, .branchLe 15 (0), .branchGe 2 (1), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchLe 13 (0), .branchGe 37 (1), .branchLe 32 (0), .branchGe 8 (1), .branchGe 14 (1)]

def plane484GenLeaf0279Mult : Fin 43 → Nat := ![127, 93, 109, 16, 31, 55, 81, 35, 14, 34, 14, 18, 4, 35, 8, 30, 4, 31, 34, 20, 10, 8, 38, 18, 20, 18, 127, 10, 289, 8, 39, 48, 85, 162, 88, 71, 139, 119, 18, 154, 87, 564, 414]

theorem plane484GenLeaf0279 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0279Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0279Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0279Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0279Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 216
  · exact hroot.hOcc 230
  · exact hroot.hOcc 234
  · exact hroot.hOcc 403
  · exact hroot.hOcc 572
  · exact hroot.hOcc 784
  · exact hroot.hOcc 1180
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1223
  · exact hroot.hOcc 1302
  · exact hroot.hOcc 1383
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1507
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1528
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1608
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
