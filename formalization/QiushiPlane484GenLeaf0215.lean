import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0215Refs : Fin 44 → RowRef 1665 43 := ![.occ 141, .occ 160, .occ 175, .occ 216, .occ 220, .occ 242, .occ 379, .occ 386, .occ 395, .occ 470, .occ 525, .occ 591, .occ 775, .occ 860, .occ 1132, .occ 1168, .occ 1170, .occ 1208, .occ 1214, .occ 1220, .occ 1222, .occ 1236, .occ 1287, .occ 1411, .occ 1442, .occ 1467, .occ 1511, .occ 1516, .occ 1559, .occ 1597, .occ 1601, .sumGe, .nonneg 19, .nonneg 23, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchGe 16 (1), .branchLe 37 (0), .branchLe 22 (0), .branchGe 27 (1), .branchLe 5 (0), .branchGe 20 (1)]

def plane484GenLeaf0215Mult : Fin 44 → Nat := ![24, 32, 21, 29, 25, 18, 26, 90, 34, 12, 7, 11, 14, 95, 12, 7, 27, 5, 5, 30, 53, 9, 44, 43, 52, 12, 57, 2, 43, 9, 5, 126, 76, 277, 102, 36, 228, 277, 501, 126, 31, 248, 115, 392]

theorem plane484GenLeaf0215 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0215Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0215Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0215Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0215Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 141
  · exact hroot.hOcc 160
  · exact hroot.hOcc 175
  · exact hroot.hOcc 216
  · exact hroot.hOcc 220
  · exact hroot.hOcc 242
  · exact hroot.hOcc 379
  · exact hroot.hOcc 386
  · exact hroot.hOcc 395
  · exact hroot.hOcc 470
  · exact hroot.hOcc 525
  · exact hroot.hOcc 591
  · exact hroot.hOcc 775
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1132
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1287
  · exact hroot.hOcc 1411
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1511
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1559
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1601
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
