import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0237Refs : Fin 42 → RowRef 1665 43 := ![.occ 106, .occ 120, .occ 121, .occ 124, .occ 125, .occ 128, .occ 136, .occ 203, .occ 302, .occ 371, .occ 388, .occ 708, .occ 793, .occ 853, .occ 858, .occ 1109, .occ 1145, .occ 1150, .occ 1186, .occ 1369, .occ 1429, .occ 1451, .occ 1472, .occ 1597, .occ 1602, .occ 1610, .occ 1647, .occ 1657, .sumGe, .nonneg 4, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchLe 16 (0), .branchGe 31 (1), .branchLe 20 (0), .branchLe 30 (0), .branchGe 5 (1)]

def plane484GenLeaf0237Mult : Fin 42 → Nat := ![28, 45, 19, 66, 44, 33, 24, 4, 16, 100, 16, 39, 36, 36, 36, 16, 72, 8, 8, 4, 4, 4, 36, 40, 12, 52, 4, 12, 148, 62, 112, 122, 8, 136, 148, 148, 68, 108, 24, 88, 140, 506]

theorem plane484GenLeaf0237 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0237Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0237Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0237Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0237Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 106
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 136
  · exact hroot.hOcc 203
  · exact hroot.hOcc 302
  · exact hroot.hOcc 371
  · exact hroot.hOcc 388
  · exact hroot.hOcc 708
  · exact hroot.hOcc 793
  · exact hroot.hOcc 853
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1109
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1369
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1451
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
