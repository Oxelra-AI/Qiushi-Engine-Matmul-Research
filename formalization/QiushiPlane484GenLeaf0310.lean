import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0310Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 124, .occ 125, .occ 128, .occ 136, .occ 172, .occ 179, .occ 184, .occ 185, .occ 344, .occ 350, .occ 456, .occ 605, .occ 1111, .occ 1136, .occ 1170, .occ 1179, .occ 1183, .occ 1188, .occ 1191, .occ 1196, .occ 1220, .occ 1353, .occ 1477, .occ 1488, .occ 1491, .occ 1519, .occ 1580, .occ 1597, .occ 1644, .sumGe, .nonneg 3, .nonneg 13, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchGe 34 (1), .branchGe 36 (1), .branchLe 42 (0), .branchGe 30 (1), .branchGe 12 (1)]

def plane484GenLeaf0310Mult : Fin 44 → Nat := ![753, 1021, 144, 445, 721, 338, 94, 36, 81, 195, 1560, 122, 81, 291, 362, 230, 504, 273, 77, 622, 260, 474, 933, 87, 399, 516, 60, 444, 134, 258, 1999, 469, 655, 1922, 3045, 60, 1495, 1555, 1051, 3405, 3269, 997, 2657, 4647]

theorem plane484GenLeaf0310 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0310Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0310Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0310Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0310Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 136
  · exact hroot.hOcc 172
  · exact hroot.hOcc 179
  · exact hroot.hOcc 184
  · exact hroot.hOcc 185
  · exact hroot.hOcc 344
  · exact hroot.hOcc 350
  · exact hroot.hOcc 456
  · exact hroot.hOcc 605
  · exact hroot.hOcc 1111
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1519
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1644
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
