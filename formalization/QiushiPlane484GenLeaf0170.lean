import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0170Refs : Fin 38 → RowRef 1665 43 := ![.occ 131, .occ 135, .occ 140, .occ 145, .occ 665, .occ 686, .occ 723, .occ 881, .occ 967, .occ 998, .occ 1166, .occ 1196, .occ 1310, .occ 1317, .occ 1323, .occ 1343, .occ 1380, .occ 1402, .occ 1443, .occ 1459, .occ 1486, .sumGe, .nonneg 0, .nonneg 1, .nonneg 2, .nonneg 3, .nonneg 15, .nonneg 16, .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchGe 30 (1), .branchGe 20 (1), .branchLe 5 (0), .branchLe 31 (0), .branchLe 6 (0), .branchGe 24 (1)]

def plane484GenLeaf0170Mult : Fin 38 → Nat := ![3, 8, 9, 7, 1, 9, 3, 1, 2, 1, 3, 2, 5, 1, 5, 2, 2, 1, 1, 2, 1, 10, 3, 1, 1, 3, 21, 1, 8, 9, 16, 2, 18, 30, 4, 10, 4, 40]

theorem plane484GenLeaf0170 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0170Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0170Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0170Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0170Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 131
  · exact hroot.hOcc 135
  · exact hroot.hOcc 140
  · exact hroot.hOcc 145
  · exact hroot.hOcc 665
  · exact hroot.hOcc 686
  · exact hroot.hOcc 723
  · exact hroot.hOcc 881
  · exact hroot.hOcc 967
  · exact hroot.hOcc 998
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1310
  · exact hroot.hOcc 1317
  · exact hroot.hOcc 1323
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1380
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1443
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1486
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
