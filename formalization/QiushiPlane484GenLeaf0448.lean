import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0448Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 124, .occ 129, .occ 133, .occ 134, .occ 135, .occ 137, .occ 138, .occ 335, .occ 348, .occ 360, .occ 418, .occ 693, .occ 859, .occ 957, .occ 1140, .occ 1147, .occ 1252, .occ 1329, .occ 1396, .occ 1415, .occ 1424, .occ 1434, .occ 1473, .occ 1610, .occ 1630, .occ 1631, .occ 1639, .occ 1651, .occ 1658, .sumGe, .nonneg 1, .nonneg 2, .nonneg 10, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchLe 29 (0), .branchGe 23 (1), .branchGe 3 (1), .branchLe 33 (0), .branchGe 20 (1)]

def plane484GenLeaf0448Mult : Fin 44 → Nat := ![3626, 2168, 54, 2368, 1825, 3145, 3440, 877, 6585, 9564, 874, 2564, 1560, 28, 894, 684, 328, 1174, 4428, 3380, 1550, 846, 3400, 1912, 164, 164, 2740, 3404, 2268, 372, 2366, 14180, 2332, 1112, 194, 14208, 14180, 194, 8022, 13852, 17074, 18250, 14180, 28196]

theorem plane484GenLeaf0448 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0448Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0448Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0448Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0448Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 335
  · exact hroot.hOcc 348
  · exact hroot.hOcc 360
  · exact hroot.hOcc 418
  · exact hroot.hOcc 693
  · exact hroot.hOcc 859
  · exact hroot.hOcc 957
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1252
  · exact hroot.hOcc 1329
  · exact hroot.hOcc 1396
  · exact hroot.hOcc 1415
  · exact hroot.hOcc 1424
  · exact hroot.hOcc 1434
  · exact hroot.hOcc 1473
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1651
  · exact hroot.hOcc 1658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
