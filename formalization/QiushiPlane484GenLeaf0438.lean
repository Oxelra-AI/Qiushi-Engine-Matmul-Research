import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0438Refs : Fin 44 → RowRef 1665 43 := ![.occ 95, .occ 121, .occ 128, .occ 133, .occ 138, .occ 186, .occ 244, .occ 257, .occ 269, .occ 513, .occ 612, .occ 693, .occ 825, .occ 958, .occ 1188, .occ 1226, .occ 1261, .occ 1281, .occ 1318, .occ 1329, .occ 1334, .occ 1348, .occ 1350, .occ 1400, .occ 1409, .occ 1459, .occ 1483, .occ 1597, .occ 1631, .occ 1642, .occ 1658, .sumGe, .nonneg 18, .nonneg 23, .branchGe 15 (1), .branchLe 7 (0), .branchLe 0 (0), .branchLe 29 (0), .branchGe 19 (1), .branchLe 31 (0), .branchLe 20 (0), .branchGe 38 (1), .branchLe 17 (0), .branchGe 28 (1)]

def plane484GenLeaf0438Mult : Fin 44 → Nat := ![3, 1, 1, 10, 18, 15, 1, 13, 12, 6, 13, 25, 2, 6, 1, 3, 19, 4, 1, 3, 11, 1, 1, 3, 5, 5, 13, 8, 7, 1, 1, 33, 3, 9, 85, 18, 33, 33, 74, 25, 30, 95, 15, 101]

theorem plane484GenLeaf0438 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0438Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0438Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0438Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0438Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 121
  · exact hroot.hOcc 128
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 186
  · exact hroot.hOcc 244
  · exact hroot.hOcc 257
  · exact hroot.hOcc 269
  · exact hroot.hOcc 513
  · exact hroot.hOcc 612
  · exact hroot.hOcc 693
  · exact hroot.hOcc 825
  · exact hroot.hOcc 958
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1226
  · exact hroot.hOcc 1261
  · exact hroot.hOcc 1281
  · exact hroot.hOcc 1318
  · exact hroot.hOcc 1329
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1400
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1642
  · exact hroot.hOcc 1658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
