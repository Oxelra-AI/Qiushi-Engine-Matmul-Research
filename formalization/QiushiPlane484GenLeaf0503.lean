import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0503Refs : Fin 38 → RowRef 1665 43 := ![.occ 119, .occ 124, .occ 126, .occ 138, .occ 142, .occ 177, .occ 186, .occ 260, .occ 514, .occ 581, .occ 596, .occ 682, .occ 783, .occ 1052, .occ 1068, .occ 1174, .occ 1218, .occ 1271, .occ 1276, .occ 1297, .occ 1344, .occ 1350, .occ 1467, .occ 1572, .occ 1590, .occ 1621, .occ 1629, .occ 1658, .occ 1660, .occ 1664, .sumGe, .nonneg 2, .branchGe 15 (1), .branchLe 35 (0), .branchGe 7 (1), .branchGe 32 (1), .branchLe 39 (0), .branchGe 10 (1)]

def plane484GenLeaf0503Mult : Fin 38 → Nat := ![1430, 2074, 2976, 1494, 1474, 1430, 1612, 636, 4930, 22, 1292, 636, 1442, 204, 284, 1430, 574, 254, 102, 2454, 92, 102, 1960, 3172, 1336, 1395, 1267, 81, 1085, 138, 6096, 3620, 20670, 6096, 13530, 13482, 4666, 15392]

theorem plane484GenLeaf0503 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0503Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0503Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0503Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0503Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 177
  · exact hroot.hOcc 186
  · exact hroot.hOcc 260
  · exact hroot.hOcc 514
  · exact hroot.hOcc 581
  · exact hroot.hOcc 596
  · exact hroot.hOcc 682
  · exact hroot.hOcc 783
  · exact hroot.hOcc 1052
  · exact hroot.hOcc 1068
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1218
  · exact hroot.hOcc 1271
  · exact hroot.hOcc 1276
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1344
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1572
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1621
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1658
  · exact hroot.hOcc 1660
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
