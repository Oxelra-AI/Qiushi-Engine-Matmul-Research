import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0092Refs : Fin 42 → RowRef 1665 43 := ![.occ 131, .occ 132, .occ 134, .occ 141, .occ 179, .occ 337, .occ 352, .occ 804, .occ 853, .occ 998, .occ 1055, .occ 1079, .occ 1084, .occ 1091, .occ 1143, .occ 1145, .occ 1256, .occ 1289, .occ 1291, .occ 1300, .occ 1336, .occ 1351, .occ 1451, .occ 1478, .occ 1609, .occ 1610, .occ 1620, .occ 1655, .occ 1663, .sumGe, .nonneg 0, .nonneg 10, .nonneg 21, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchLe 26 (0), .branchGe 24 (1), .branchLe 7 (0), .branchGe 18 (1)]

def plane484GenLeaf0092Mult : Fin 42 → Nat := ![44, 80, 62, 22, 132, 40, 24, 44, 76, 114, 12, 57, 83, 40, 76, 12, 4, 39, 18, 23, 40, 26, 68, 44, 38, 10, 66, 26, 48, 264, 44, 66, 252, 220, 176, 264, 556, 264, 176, 584, 66, 596]

theorem plane484GenLeaf0092 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0092Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0092Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0092Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0092Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 141
  · exact hroot.hOcc 179
  · exact hroot.hOcc 337
  · exact hroot.hOcc 352
  · exact hroot.hOcc 804
  · exact hroot.hOcc 853
  · exact hroot.hOcc 998
  · exact hroot.hOcc 1055
  · exact hroot.hOcc 1079
  · exact hroot.hOcc 1084
  · exact hroot.hOcc 1091
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1289
  · exact hroot.hOcc 1291
  · exact hroot.hOcc 1300
  · exact hroot.hOcc 1336
  · exact hroot.hOcc 1351
  · exact hroot.hOcc 1451
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
