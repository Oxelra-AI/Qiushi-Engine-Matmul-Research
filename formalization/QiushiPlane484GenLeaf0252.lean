import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0252Refs : Fin 40 → RowRef 1665 43 := ![.occ 124, .occ 126, .occ 130, .occ 136, .occ 290, .occ 482, .occ 512, .occ 526, .occ 645, .occ 776, .occ 1005, .occ 1150, .occ 1158, .occ 1173, .occ 1183, .occ 1204, .occ 1208, .occ 1281, .occ 1282, .occ 1309, .occ 1358, .occ 1442, .occ 1470, .occ 1489, .occ 1648, .occ 1656, .sumGe, .nonneg 6, .nonneg 7, .branchLe 15 (0), .branchGe 2 (1), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchGe 16 (1), .branchLe 13 (0), .branchGe 41 (1), .branchGe 40 (1), .branchGe 10 (1)]

def plane484GenLeaf0252Mult : Fin 40 → Nat := ![5, 4, 4, 12, 8, 7, 4, 1, 11, 2, 3, 1, 1, 1, 5, 5, 1, 1, 1, 1, 1, 4, 7, 2, 1, 1, 15, 2, 1, 12, 14, 8, 14, 14, 3, 33, 1, 15, 11, 52]

theorem plane484GenLeaf0252 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0252Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0252Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0252Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0252Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 130
  · exact hroot.hOcc 136
  · exact hroot.hOcc 290
  · exact hroot.hOcc 482
  · exact hroot.hOcc 512
  · exact hroot.hOcc 526
  · exact hroot.hOcc 645
  · exact hroot.hOcc 776
  · exact hroot.hOcc 1005
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1204
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1281
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1309
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1648
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
