import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0149Refs : Fin 43 → RowRef 1665 43 := ![.occ 140, .occ 141, .occ 150, .occ 334, .occ 342, .occ 375, .occ 417, .occ 478, .occ 486, .occ 625, .occ 665, .occ 743, .occ 819, .occ 1001, .occ 1136, .occ 1151, .occ 1215, .occ 1269, .occ 1283, .occ 1296, .occ 1308, .occ 1337, .occ 1407, .occ 1459, .occ 1523, .occ 1553, .occ 1601, .occ 1626, .occ 1661, .sumGe, .nonneg 9, .nonneg 22, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 39 (1), .branchLe 16 (0), .branchGe 27 (1), .branchGe 24 (1), .branchLe 8 (0), .branchGe 17 (1)]

def plane484GenLeaf0149Mult : Fin 43 → Nat := ![276, 55, 22, 160, 34, 256, 22, 40, 353, 207, 52, 64, 65, 64, 112, 95, 55, 143, 126, 19, 20, 176, 55, 150, 53, 32, 55, 102, 252, 576, 97, 54, 300, 576, 460, 576, 502, 1292, 576, 821, 904, 503, 1229]

theorem plane484GenLeaf0149 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0149Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0149Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0149Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0149Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 150
  · exact hroot.hOcc 334
  · exact hroot.hOcc 342
  · exact hroot.hOcc 375
  · exact hroot.hOcc 417
  · exact hroot.hOcc 478
  · exact hroot.hOcc 486
  · exact hroot.hOcc 625
  · exact hroot.hOcc 665
  · exact hroot.hOcc 743
  · exact hroot.hOcc 819
  · exact hroot.hOcc 1001
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1283
  · exact hroot.hOcc 1296
  · exact hroot.hOcc 1308
  · exact hroot.hOcc 1337
  · exact hroot.hOcc 1407
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1523
  · exact hroot.hOcc 1553
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
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
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
