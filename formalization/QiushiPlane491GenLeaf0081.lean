import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0081Refs : Fin 50 → RowRef 726 49 := ![.occ 87, .occ 88, .occ 90, .occ 98, .occ 105, .occ 118, .occ 123, .occ 143, .occ 144, .occ 149, .occ 155, .occ 167, .occ 170, .occ 171, .occ 191, .occ 231, .occ 234, .occ 240, .occ 241, .occ 267, .occ 313, .occ 334, .occ 351, .occ 355, .occ 358, .occ 379, .occ 393, .occ 394, .occ 401, .occ 410, .occ 413, .occ 423, .occ 425, .occ 482, .occ 543, .occ 548, .occ 621, .occ 671, .occ 685, .occ 692, .occ 714, .occ 725, .sumGe, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchLe 27 (0), .branchGe 22 (1), .branchLe 3 (0), .branchGe 23 (1)]

def plane491GenLeaf0081Mult : Fin 50 → Nat := ![2042, 2360, 1568, 2083, 1455, 1762, 1033, 503, 1558, 791, 12, 1109, 1705, 1512, 393, 29, 199, 547, 679, 169, 105, 910, 453, 1072, 745, 396, 824, 104, 1022, 1013, 150, 429, 91, 425, 269, 219, 982, 1008, 795, 872, 46, 101, 3155, 10203, 2886, 3155, 2283, 8201, 3155, 9113]

theorem plane491GenLeaf0081 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0081Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0081Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0081Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0081Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 98
  · exact hroot.hOcc 105
  · exact hroot.hOcc 118
  · exact hroot.hOcc 123
  · exact hroot.hOcc 143
  · exact hroot.hOcc 144
  · exact hroot.hOcc 149
  · exact hroot.hOcc 155
  · exact hroot.hOcc 167
  · exact hroot.hOcc 170
  · exact hroot.hOcc 171
  · exact hroot.hOcc 191
  · exact hroot.hOcc 231
  · exact hroot.hOcc 234
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · exact hroot.hOcc 267
  · exact hroot.hOcc 313
  · exact hroot.hOcc 334
  · exact hroot.hOcc 351
  · exact hroot.hOcc 355
  · exact hroot.hOcc 358
  · exact hroot.hOcc 379
  · exact hroot.hOcc 393
  · exact hroot.hOcc 394
  · exact hroot.hOcc 401
  · exact hroot.hOcc 410
  · exact hroot.hOcc 413
  · exact hroot.hOcc 423
  · exact hroot.hOcc 425
  · exact hroot.hOcc 482
  · exact hroot.hOcc 543
  · exact hroot.hOcc 548
  · exact hroot.hOcc 621
  · exact hroot.hOcc 671
  · exact hroot.hOcc 685
  · exact hroot.hOcc 692
  · exact hroot.hOcc 714
  · exact hroot.hOcc 725
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (22 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (3 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (23 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23

end QiushiMatmul
