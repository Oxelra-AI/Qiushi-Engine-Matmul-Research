import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0020Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 120, .occ 128, .occ 132, .occ 139, .occ 141, .occ 330, .occ 771, .occ 781, .occ 839, .occ 1006, .occ 1150, .occ 1163, .occ 1166, .occ 1168, .occ 1172, .occ 1185, .occ 1196, .occ 1207, .occ 1281, .occ 1357, .occ 1399, .occ 1403, .occ 1470, .occ 1532, .occ 1597, .occ 1602, .occ 1608, .occ 1647, .occ 1655, .occ 1658, .occ 1664, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchGe 41 (1), .branchGe 19 (1), .branchGe 10 (1), .branchGe 0 (1)]

def plane484GenLeaf0020Mult : Fin 44 → Nat := ![12455, 51979, 20955, 29868, 1895, 12665, 41311, 10777, 15284, 234, 31114, 24684, 5384, 1211, 44243, 10166, 32489, 3498, 13596, 13862, 6266, 2859, 9384, 15343, 3539, 13397, 27915, 16445, 3594, 12618, 3874, 8355, 106362, 52822, 66781, 105151, 60868, 60868, 52822, 86699, 77512, 152223, 166215, 161901]

theorem plane484GenLeaf0020 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0020Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0020Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0020Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0020Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 330
  · exact hroot.hOcc 771
  · exact hroot.hOcc 781
  · exact hroot.hOcc 839
  · exact hroot.hOcc 1006
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1163
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1185
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1207
  · exact hroot.hOcc 1281
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1399
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1532
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1658
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
