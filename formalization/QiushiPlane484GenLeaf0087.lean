import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0087Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 127, .occ 128, .occ 130, .occ 403, .occ 418, .occ 424, .occ 650, .occ 699, .occ 853, .occ 1150, .occ 1174, .occ 1208, .occ 1213, .occ 1237, .occ 1243, .occ 1244, .occ 1246, .occ 1249, .occ 1256, .occ 1304, .occ 1314, .occ 1382, .occ 1395, .occ 1442, .occ 1448, .occ 1478, .occ 1546, .occ 1610, .occ 1620, .occ 1639, .occ 1657, .sumGe, .nonneg 6, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchLe 26 (0), .branchLe 24 (0), .branchLe 19 (0), .branchGe 31 (1), .branchGe 41 (1)]

def plane484GenLeaf0087Mult : Fin 44 → Nat := ![73, 108, 17, 189, 13, 10, 27, 102, 21, 207, 78, 4, 3, 7, 60, 99, 68, 136, 107, 2, 3, 29, 26, 26, 34, 61, 161, 69, 116, 46, 2, 46, 424, 65, 314, 422, 424, 998, 378, 350, 424, 300, 494, 817]

theorem plane484GenLeaf0087 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0087Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0087Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0087Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0087Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 403
  · exact hroot.hOcc 418
  · exact hroot.hOcc 424
  · exact hroot.hOcc 650
  · exact hroot.hOcc 699
  · exact hroot.hOcc 853
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1237
  · exact hroot.hOcc 1243
  · exact hroot.hOcc 1244
  · exact hroot.hOcc 1246
  · exact hroot.hOcc 1249
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1304
  · exact hroot.hOcc 1314
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1395
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1448
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41

end QiushiMatmul
