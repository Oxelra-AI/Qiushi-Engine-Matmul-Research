import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0369Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 125, .occ 126, .occ 128, .occ 133, .occ 134, .occ 136, .occ 137, .occ 138, .occ 139, .occ 147, .occ 149, .occ 193, .occ 288, .occ 434, .occ 752, .occ 859, .occ 1136, .occ 1143, .occ 1146, .occ 1151, .occ 1215, .occ 1228, .occ 1240, .occ 1290, .occ 1291, .occ 1441, .occ 1459, .occ 1462, .occ 1477, .occ 1491, .occ 1573, .occ 1664, .sumGe, .nonneg 26, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchLe 35 (0), .branchGe 3 (1), .branchLe 9 (0), .branchGe 1 (1), .branchLe 0 (0)]

def plane484GenLeaf0369Mult : Fin 44 → Nat := ![91, 28, 129, 1153, 360, 356, 11, 816, 712, 119, 39, 55, 19, 621, 253, 26, 77, 208, 46, 527, 100, 608, 130, 9, 139, 25, 161, 467, 224, 316, 294, 307, 46, 1534, 1779, 416, 1413, 1325, 3235, 1227, 1959, 1299, 2260, 1280]

theorem plane484GenLeaf0369 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0369Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0369Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0369Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0369Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 147
  · exact hroot.hOcc 149
  · exact hroot.hOcc 193
  · exact hroot.hOcc 288
  · exact hroot.hOcc 434
  · exact hroot.hOcc 752
  · exact hroot.hOcc 859
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1228
  · exact hroot.hOcc 1240
  · exact hroot.hOcc 1290
  · exact hroot.hOcc 1291
  · exact hroot.hOcc 1441
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
