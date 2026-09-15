import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0316Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 120, .occ 135, .occ 137, .occ 474, .occ 536, .occ 667, .occ 707, .occ 1143, .occ 1146, .occ 1147, .occ 1164, .occ 1166, .occ 1168, .occ 1216, .occ 1220, .occ 1289, .occ 1306, .occ 1357, .occ 1398, .occ 1451, .occ 1491, .occ 1496, .occ 1561, .occ 1573, .occ 1603, .occ 1606, .occ 1608, .occ 1610, .occ 1643, .sumGe, .nonneg 23, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 26 (1), .branchLe 14 (0), .branchLe 1 (0), .branchLe 22 (0), .branchLe 16 (0), .branchGe 0 (1), .branchGe 31 (1), .branchLe 19 (0), .branchLe 13 (0)]

def plane484GenLeaf0316Mult : Fin 44 → Nat := ![3852, 8208, 992, 9302, 1898, 2698, 2012, 9526, 643, 7588, 4448, 170, 1472, 5722, 1965, 720, 3362, 5184, 3540, 686, 2706, 154, 9133, 1570, 3786, 1250, 3361, 4480, 1712, 686, 23482, 20004, 22490, 13250, 13508, 40120, 23482, 23482, 22232, 13494, 22496, 11922, 13236, 22796]

theorem plane484GenLeaf0316 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0316Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0316Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0316Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0316Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 474
  · exact hroot.hOcc 536
  · exact hroot.hOcc 667
  · exact hroot.hOcc 707
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1289
  · exact hroot.hOcc 1306
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1451
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1561
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1643
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13

end QiushiMatmul
