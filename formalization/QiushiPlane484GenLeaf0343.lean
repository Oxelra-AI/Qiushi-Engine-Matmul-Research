import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0343Refs : Fin 42 → RowRef 1665 43 := ![.occ 125, .occ 126, .occ 134, .occ 136, .occ 137, .occ 142, .occ 175, .occ 347, .occ 452, .occ 463, .occ 466, .occ 631, .occ 743, .occ 818, .occ 1023, .occ 1134, .occ 1172, .occ 1179, .occ 1271, .occ 1354, .occ 1363, .occ 1386, .occ 1393, .occ 1436, .occ 1462, .occ 1492, .occ 1522, .occ 1551, .occ 1630, .occ 1632, .sumGe, .nonneg 11, .nonneg 19, .nonneg 21, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 26 (1), .branchGe 14 (1), .branchLe 36 (0), .branchLe 28 (0), .branchGe 27 (1)]

def plane484GenLeaf0343Mult : Fin 42 → Nat := ![1361, 1093, 76, 152, 1253, 76, 313, 88, 164, 102, 198, 1147, 309, 1089, 193, 164, 1049, 701, 142, 645, 111, 76, 76, 76, 905, 240, 385, 480, 68, 444, 2194, 260, 76, 628, 1592, 2069, 404, 5119, 8617, 1289, 2126, 3585]

theorem plane484GenLeaf0343 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0343Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0343Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0343Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0343Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 142
  · exact hroot.hOcc 175
  · exact hroot.hOcc 347
  · exact hroot.hOcc 452
  · exact hroot.hOcc 463
  · exact hroot.hOcc 466
  · exact hroot.hOcc 631
  · exact hroot.hOcc 743
  · exact hroot.hOcc 818
  · exact hroot.hOcc 1023
  · exact hroot.hOcc 1134
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1271
  · exact hroot.hOcc 1354
  · exact hroot.hOcc 1363
  · exact hroot.hOcc 1386
  · exact hroot.hOcc 1393
  · exact hroot.hOcc 1436
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1551
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1632
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27

end QiushiMatmul
