import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0162Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 122, .occ 127, .occ 139, .occ 206, .occ 232, .occ 259, .occ 261, .occ 777, .occ 808, .occ 979, .occ 1058, .occ 1151, .occ 1216, .occ 1224, .occ 1239, .occ 1258, .occ 1284, .occ 1290, .occ 1291, .occ 1468, .occ 1501, .occ 1502, .occ 1512, .occ 1557, .occ 1608, .occ 1622, .occ 1626, .occ 1635, .occ 1647, .sumGe, .nonneg 12, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchGe 30 (1), .branchLe 20 (0), .branchLe 33 (0), .branchLe 0 (0), .branchLe 14 (0), .branchLe 41 (0)]

def plane484GenLeaf0162Mult : Fin 44 → Nat := ![5866, 644, 3671, 3094, 1914, 391, 6621, 1582, 19, 1238, 1586, 947, 644, 904, 5483, 488, 1460, 4276, 1695, 661, 1144, 113, 25, 1059, 1417, 6640, 601, 2061, 5075, 383, 15063, 3323, 14462, 9605, 8628, 15063, 21549, 1864, 13368, 15038, 13255, 4857, 7763, 14575]

theorem plane484GenLeaf0162 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0162Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0162Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0162Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0162Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 127
  · exact hroot.hOcc 139
  · exact hroot.hOcc 206
  · exact hroot.hOcc 232
  · exact hroot.hOcc 259
  · exact hroot.hOcc 261
  · exact hroot.hOcc 777
  · exact hroot.hOcc 808
  · exact hroot.hOcc 979
  · exact hroot.hOcc 1058
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1224
  · exact hroot.hOcc 1239
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1284
  · exact hroot.hOcc 1290
  · exact hroot.hOcc 1291
  · exact hroot.hOcc 1468
  · exact hroot.hOcc 1501
  · exact hroot.hOcc 1502
  · exact hroot.hOcc 1512
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1635
  · exact hroot.hOcc 1647
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41

end QiushiMatmul
