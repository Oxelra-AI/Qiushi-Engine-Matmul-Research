import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0303Refs : Fin 43 → RowRef 1665 43 := ![.occ 123, .occ 125, .occ 132, .occ 134, .occ 138, .occ 168, .occ 169, .occ 181, .occ 185, .occ 614, .occ 617, .occ 626, .occ 658, .occ 734, .occ 1145, .occ 1160, .occ 1186, .occ 1200, .occ 1255, .occ 1256, .occ 1270, .occ 1286, .occ 1312, .occ 1383, .occ 1478, .occ 1484, .occ 1519, .occ 1571, .occ 1610, .occ 1655, .sumGe, .nonneg 15, .nonneg 17, .nonneg 23, .branchGe 2 (1), .branchLe 7 (0), .branchLe 26 (0), .branchGe 29 (1), .branchGe 34 (1), .branchLe 36 (0), .branchGe 22 (1), .branchLe 21 (0), .branchGe 18 (1)]

def plane484GenLeaf0303Mult : Fin 43 → Nat := ![689, 568, 1055, 1155, 1052, 464, 373, 377, 280, 228, 877, 187, 201, 503, 173, 600, 228, 273, 46, 154, 284, 364, 267, 71, 401, 680, 173, 261, 287, 386, 1942, 63, 228, 2579, 2210, 1681, 890, 3030, 2930, 1942, 4962, 574, 6072]

theorem plane484GenLeaf0303 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0303Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0303Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0303Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0303Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 138
  · exact hroot.hOcc 168
  · exact hroot.hOcc 169
  · exact hroot.hOcc 181
  · exact hroot.hOcc 185
  · exact hroot.hOcc 614
  · exact hroot.hOcc 617
  · exact hroot.hOcc 626
  · exact hroot.hOcc 658
  · exact hroot.hOcc 734
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1255
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1286
  · exact hroot.hOcc 1312
  · exact hroot.hOcc 1383
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1519
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
