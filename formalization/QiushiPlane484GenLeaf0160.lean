import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0160Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 126, .occ 127, .occ 129, .occ 137, .occ 139, .occ 175, .occ 218, .occ 234, .occ 440, .occ 508, .occ 562, .occ 820, .occ 1164, .occ 1172, .occ 1183, .occ 1215, .occ 1248, .occ 1271, .occ 1273, .occ 1353, .occ 1381, .occ 1407, .occ 1511, .occ 1526, .occ 1529, .occ 1552, .occ 1554, .occ 1601, .occ 1602, .occ 1603, .sumGe, .nonneg 0, .nonneg 6, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchLe 30 (0), .branchGe 21 (1), .branchLe 25 (0), .branchGe 14 (1)]

def plane484GenLeaf0160Mult : Fin 44 → Nat := ![108, 3564, 4076, 654, 2153, 2605, 2901, 2888, 1720, 152, 128, 1823, 683, 76, 2369, 108, 296, 108, 1707, 324, 2618, 4168, 1845, 176, 2079, 76, 440, 72, 32, 649, 391, 7085, 2605, 5261, 5378, 1260, 9699, 7085, 7732, 2451, 6977, 11899, 7085, 23262]

theorem plane484GenLeaf0160 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0160Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0160Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0160Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0160Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 175
  · exact hroot.hOcc 218
  · exact hroot.hOcc 234
  · exact hroot.hOcc 440
  · exact hroot.hOcc 508
  · exact hroot.hOcc 562
  · exact hroot.hOcc 820
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1248
  · exact hroot.hOcc 1271
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1381
  · exact hroot.hOcc 1407
  · exact hroot.hOcc 1511
  · exact hroot.hOcc 1526
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1552
  · exact hroot.hOcc 1554
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1603
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
