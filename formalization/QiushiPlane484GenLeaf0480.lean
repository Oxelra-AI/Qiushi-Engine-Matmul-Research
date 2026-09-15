import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0480Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 133, .occ 138, .occ 140, .occ 142, .occ 287, .occ 516, .occ 596, .occ 691, .occ 708, .occ 741, .occ 763, .occ 999, .occ 1136, .occ 1158, .occ 1159, .occ 1166, .occ 1187, .occ 1188, .occ 1191, .occ 1199, .occ 1216, .occ 1298, .occ 1447, .occ 1467, .occ 1470, .occ 1480, .occ 1601, .occ 1619, .sumGe, .nonneg 16, .nonneg 25, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 19 (0), .branchLe 3 (0), .branchGe 38 (1), .branchGe 34 (1), .branchLe 28 (0), .branchLe 32 (0), .branchGe 36 (1)]

def plane484GenLeaf0480Mult : Fin 43 → Nat := ![600, 832, 265, 665, 848, 453, 147, 784, 638, 272, 234, 184, 637, 50, 106, 900, 194, 100, 1278, 25, 197, 100, 185, 872, 306, 75, 13, 194, 134, 1878, 210, 100, 6966, 872, 234, 1520, 353, 1694, 51, 3367, 1693, 1778, 4309]

theorem plane484GenLeaf0480 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0480Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0480Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0480Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0480Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 287
  · exact hroot.hOcc 516
  · exact hroot.hOcc 596
  · exact hroot.hOcc 691
  · exact hroot.hOcc 708
  · exact hroot.hOcc 741
  · exact hroot.hOcc 763
  · exact hroot.hOcc 999
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1199
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1447
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1480
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1619
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36

end QiushiMatmul
