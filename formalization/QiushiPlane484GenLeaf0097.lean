import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0097Refs : Fin 43 → RowRef 1665 43 := ![.occ 125, .occ 127, .occ 130, .occ 132, .occ 139, .occ 141, .occ 193, .occ 352, .occ 366, .occ 600, .occ 744, .occ 818, .occ 855, .occ 1146, .occ 1213, .occ 1229, .occ 1284, .occ 1291, .occ 1309, .occ 1382, .occ 1424, .occ 1449, .occ 1478, .occ 1509, .occ 1541, .occ 1545, .occ 1554, .occ 1573, .occ 1632, .sumGe, .nonneg 8, .nonneg 9, .nonneg 16, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchGe 26 (1), .branchLe 37 (0), .branchGe 28 (1), .branchLe 13 (0), .branchGe 14 (1)]

def plane484GenLeaf0097Mult : Fin 43 → Nat := ![2231, 423, 917, 450, 416, 728, 10, 515, 666, 397, 690, 397, 319, 208, 726, 512, 208, 450, 641, 332, 226, 317, 492, 726, 5, 458, 257, 198, 704, 2761, 124, 1514, 373, 1357, 124, 2057, 4278, 2563, 2908, 2761, 3189, 1844, 6418]

theorem plane484GenLeaf0097 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0097Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0097Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0097Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0097Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 193
  · exact hroot.hOcc 352
  · exact hroot.hOcc 366
  · exact hroot.hOcc 600
  · exact hroot.hOcc 744
  · exact hroot.hOcc 818
  · exact hroot.hOcc 855
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1229
  · exact hroot.hOcc 1284
  · exact hroot.hOcc 1291
  · exact hroot.hOcc 1309
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1424
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1509
  · exact hroot.hOcc 1541
  · exact hroot.hOcc 1545
  · exact hroot.hOcc 1554
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1632
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
