import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0147Refs : Fin 43 → RowRef 1665 43 := ![.occ 139, .occ 311, .occ 321, .occ 334, .occ 342, .occ 352, .occ 358, .occ 553, .occ 743, .occ 1091, .occ 1145, .occ 1151, .occ 1164, .occ 1166, .occ 1248, .occ 1268, .occ 1394, .occ 1402, .occ 1422, .occ 1424, .occ 1459, .occ 1462, .occ 1491, .occ 1551, .occ 1619, .occ 1625, .occ 1653, .occ 1656, .occ 1660, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 39 (1), .branchLe 16 (0), .branchGe 27 (1), .branchGe 24 (1), .branchLe 8 (0), .branchLe 22 (0), .branchLe 17 (0), .branchLe 13 (0)]

def plane484GenLeaf0147Mult : Fin 43 → Nat := ![1238, 941, 42, 6347, 88, 1784, 1731, 2631, 2027, 1784, 2547, 3864, 1897, 4556, 1503, 2815, 626, 1318, 687, 1313, 969, 4355, 416, 108, 152, 5106, 381, 1243, 339, 12050, 8302, 9087, 20168, 12050, 5216, 25610, 5882, 10568, 15865, 2851, 11669, 6944, 10929]

theorem plane484GenLeaf0147 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0147Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0147Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0147Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0147Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 139
  · exact hroot.hOcc 311
  · exact hroot.hOcc 321
  · exact hroot.hOcc 334
  · exact hroot.hOcc 342
  · exact hroot.hOcc 352
  · exact hroot.hOcc 358
  · exact hroot.hOcc 553
  · exact hroot.hOcc 743
  · exact hroot.hOcc 1091
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1248
  · exact hroot.hOcc 1268
  · exact hroot.hOcc 1394
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1424
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1551
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1653
  · exact hroot.hOcc 1656
  · exact hroot.hOcc 1660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13

end QiushiMatmul
