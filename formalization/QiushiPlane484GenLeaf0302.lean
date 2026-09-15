import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0302Refs : Fin 41 → RowRef 1665 43 := ![.occ 95, .occ 113, .occ 120, .occ 122, .occ 123, .occ 125, .occ 130, .occ 136, .occ 181, .occ 620, .occ 758, .occ 772, .occ 1100, .occ 1140, .occ 1154, .occ 1172, .occ 1173, .occ 1186, .occ 1270, .occ 1353, .occ 1478, .occ 1481, .occ 1484, .occ 1488, .occ 1492, .occ 1571, .occ 1601, .occ 1635, .sumGe, .nonneg 19, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchGe 34 (1), .branchLe 36 (0), .branchGe 22 (1), .branchLe 21 (0), .branchLe 18 (0)]

def plane484GenLeaf0302Mult : Fin 41 → Nat := ![262, 118, 787, 570, 1031, 721, 243, 3494, 1120, 538, 726, 484, 628, 1318, 684, 1214, 316, 858, 168, 492, 1516, 184, 14, 280, 184, 1594, 290, 410, 4088, 2558, 4074, 4682, 1456, 3920, 4088, 2700, 1910, 3306, 9724, 1786, 3906]

theorem plane484GenLeaf0302 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0302Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0302Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0302Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0302Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 113
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 130
  · exact hroot.hOcc 136
  · exact hroot.hOcc 181
  · exact hroot.hOcc 620
  · exact hroot.hOcc 758
  · exact hroot.hOcc 772
  · exact hroot.hOcc 1100
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1635
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18

end QiushiMatmul
