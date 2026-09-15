import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0409Refs : Fin 44 → RowRef 1665 43 := ![.occ 124, .occ 125, .occ 126, .occ 136, .occ 137, .occ 138, .occ 140, .occ 144, .occ 179, .occ 443, .occ 504, .occ 615, .occ 726, .occ 858, .occ 1166, .occ 1208, .occ 1214, .occ 1321, .occ 1323, .occ 1447, .occ 1462, .occ 1481, .occ 1486, .occ 1489, .occ 1492, .occ 1508, .occ 1529, .occ 1545, .occ 1587, .occ 1607, .occ 1616, .sumGe, .nonneg 5, .nonneg 10, .nonneg 12, .nonneg 21, .nonneg 25, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchLe 31 (0), .branchGe 24 (1), .branchLe 38 (0)]

def plane484GenLeaf0409Mult : Fin 44 → Nat := ![593, 112, 443, 690, 148, 48, 36, 389, 3, 150, 102, 114, 68, 564, 692, 74, 20, 56, 132, 276, 114, 38, 194, 2, 114, 240, 24, 18, 446, 196, 80, 1082, 36, 148, 2, 10, 482, 158, 1864, 2970, 150, 1082, 2678, 1082]

theorem plane484GenLeaf0409 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0409Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0409Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0409Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0409Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 144
  · exact hroot.hOcc 179
  · exact hroot.hOcc 443
  · exact hroot.hOcc 504
  · exact hroot.hOcc 615
  · exact hroot.hOcc 726
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1321
  · exact hroot.hOcc 1323
  · exact hroot.hOcc 1447
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1508
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1545
  · exact hroot.hOcc 1587
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1616
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38

end QiushiMatmul
