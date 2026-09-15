import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0504Refs : Fin 39 → RowRef 1665 43 := ![.occ 126, .occ 129, .occ 131, .occ 133, .occ 138, .occ 145, .occ 314, .occ 500, .occ 514, .occ 554, .occ 682, .occ 683, .occ 778, .occ 844, .occ 869, .occ 967, .occ 1164, .occ 1174, .occ 1186, .occ 1196, .occ 1205, .occ 1235, .occ 1294, .occ 1377, .occ 1467, .occ 1510, .occ 1514, .occ 1550, .occ 1590, .occ 1608, .occ 1633, .sumGe, .nonneg 24, .branchGe 15 (1), .branchLe 35 (0), .branchGe 7 (1), .branchGe 32 (1), .branchGe 39 (1), .branchLe 17 (0)]

def plane484GenLeaf0504Mult : Fin 39 → Nat := ![67, 1, 30, 22, 13, 33, 7, 26, 13, 22, 10, 29, 16, 21, 1, 39, 35, 79, 2, 18, 2, 22, 8, 69, 5, 8, 23, 46, 1, 10, 9, 109, 17, 236, 15, 441, 311, 190, 71]

theorem plane484GenLeaf0504 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0504Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0504Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0504Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0504Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 126
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 145
  · exact hroot.hOcc 314
  · exact hroot.hOcc 500
  · exact hroot.hOcc 514
  · exact hroot.hOcc 554
  · exact hroot.hOcc 682
  · exact hroot.hOcc 683
  · exact hroot.hOcc 778
  · exact hroot.hOcc 844
  · exact hroot.hOcc 869
  · exact hroot.hOcc 967
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1235
  · exact hroot.hOcc 1294
  · exact hroot.hOcc 1377
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1510
  · exact hroot.hOcc 1514
  · exact hroot.hOcc 1550
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1633
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17

end QiushiMatmul
