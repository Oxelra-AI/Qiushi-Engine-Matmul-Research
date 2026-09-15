import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0529Refs : Fin 40 → RowRef 1665 43 := ![.occ 123, .occ 126, .occ 138, .occ 144, .occ 175, .occ 191, .occ 221, .occ 296, .occ 380, .occ 381, .occ 432, .occ 596, .occ 640, .occ 647, .occ 691, .occ 1097, .occ 1159, .occ 1276, .occ 1320, .occ 1330, .occ 1391, .occ 1418, .occ 1426, .occ 1467, .occ 1559, .occ 1560, .occ 1597, .occ 1615, .occ 1617, .occ 1637, .sumGe, .nonneg 13, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchGe 34 (1), .branchGe 9 (1), .branchGe 3 (1)]

def plane484GenLeaf0529Mult : Fin 40 → Nat := ![53, 4, 41, 60, 59, 19, 31, 31, 2, 95, 22, 14, 50, 12, 51, 7, 3, 4, 22, 3, 13, 36, 35, 6, 22, 30, 35, 8, 31, 3, 101, 188, 236, 289, 60, 22, 101, 260, 346, 430]

theorem plane484GenLeaf0529 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0529Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0529Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0529Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0529Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 138
  · exact hroot.hOcc 144
  · exact hroot.hOcc 175
  · exact hroot.hOcc 191
  · exact hroot.hOcc 221
  · exact hroot.hOcc 296
  · exact hroot.hOcc 380
  · exact hroot.hOcc 381
  · exact hroot.hOcc 432
  · exact hroot.hOcc 596
  · exact hroot.hOcc 640
  · exact hroot.hOcc 647
  · exact hroot.hOcc 691
  · exact hroot.hOcc 1097
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1276
  · exact hroot.hOcc 1320
  · exact hroot.hOcc 1330
  · exact hroot.hOcc 1391
  · exact hroot.hOcc 1418
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1559
  · exact hroot.hOcc 1560
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1617
  · exact hroot.hOcc 1637
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
