import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0151Refs : Fin 40 → RowRef 1665 43 := ![.occ 122, .occ 125, .occ 139, .occ 309, .occ 448, .occ 449, .occ 553, .occ 678, .occ 784, .occ 971, .occ 972, .occ 974, .occ 989, .occ 1164, .occ 1269, .occ 1289, .occ 1302, .occ 1337, .occ 1339, .occ 1381, .occ 1386, .occ 1419, .occ 1427, .occ 1521, .occ 1593, .occ 1625, .occ 1630, .occ 1645, .occ 1661, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 39 (1), .branchLe 16 (0), .branchGe 27 (1), .branchGe 24 (1), .branchGe 8 (1)]

def plane484GenLeaf0151Mult : Fin 40 → Nat := ![27, 6, 39, 74, 95, 73, 20, 17, 60, 22, 16, 16, 13, 95, 17, 15, 31, 18, 11, 3, 1, 1, 18, 8, 45, 11, 23, 33, 28, 134, 28, 95, 230, 134, 39, 169, 63, 328, 390, 494]

theorem plane484GenLeaf0151 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0151Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0151Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0151Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0151Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 139
  · exact hroot.hOcc 309
  · exact hroot.hOcc 448
  · exact hroot.hOcc 449
  · exact hroot.hOcc 553
  · exact hroot.hOcc 678
  · exact hroot.hOcc 784
  · exact hroot.hOcc 971
  · exact hroot.hOcc 972
  · exact hroot.hOcc 974
  · exact hroot.hOcc 989
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1289
  · exact hroot.hOcc 1302
  · exact hroot.hOcc 1337
  · exact hroot.hOcc 1339
  · exact hroot.hOcc 1381
  · exact hroot.hOcc 1386
  · exact hroot.hOcc 1419
  · exact hroot.hOcc 1427
  · exact hroot.hOcc 1521
  · exact hroot.hOcc 1593
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1645
  · exact hroot.hOcc 1661
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
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
