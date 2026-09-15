import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0306Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 126, .occ 135, .occ 180, .occ 187, .occ 235, .occ 239, .occ 332, .occ 478, .occ 617, .occ 1116, .occ 1136, .occ 1143, .occ 1154, .occ 1159, .occ 1180, .occ 1191, .occ 1214, .occ 1262, .occ 1353, .occ 1471, .occ 1488, .occ 1518, .occ 1538, .occ 1567, .occ 1597, .occ 1601, .occ 1610, .occ 1649, .occ 1652, .sumGe, .nonneg 39, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchGe 34 (1), .branchGe 36 (1), .branchLe 42 (0), .branchLe 30 (0), .branchLe 27 (0), .branchGe 37 (1)]

def plane484GenLeaf0306Mult : Fin 44 → Nat := ![368, 1202, 1248, 482, 2322, 864, 3130, 220, 1784, 2940, 216, 1377, 774, 291, 1208, 392, 556, 288, 49, 216, 1215, 928, 170, 409, 468, 1248, 1421, 48, 598, 846, 4486, 978, 1184, 1932, 3284, 3042, 4198, 12486, 14260, 9360, 874, 2818, 2682, 5758]

theorem plane484GenLeaf0306 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0306Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0306Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0306Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0306Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 135
  · exact hroot.hOcc 180
  · exact hroot.hOcc 187
  · exact hroot.hOcc 235
  · exact hroot.hOcc 239
  · exact hroot.hOcc 332
  · exact hroot.hOcc 478
  · exact hroot.hOcc 617
  · exact hroot.hOcc 1116
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1180
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1262
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1518
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1649
  · exact hroot.hOcc 1652
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
