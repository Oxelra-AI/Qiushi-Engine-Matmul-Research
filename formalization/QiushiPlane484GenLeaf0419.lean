import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0419Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 124, .occ 126, .occ 127, .occ 137, .occ 138, .occ 139, .occ 307, .occ 474, .occ 506, .occ 838, .occ 841, .occ 1151, .occ 1154, .occ 1164, .occ 1173, .occ 1186, .occ 1208, .occ 1302, .occ 1320, .occ 1357, .occ 1481, .occ 1486, .occ 1496, .occ 1507, .occ 1529, .occ 1546, .occ 1567, .occ 1590, .occ 1608, .occ 1663, .sumGe, .nonneg 8, .nonneg 13, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchGe 31 (1), .branchGe 29 (1), .branchLe 36 (0), .branchLe 34 (0), .branchLe 20 (0), .branchGe 40 (1)]

def plane484GenLeaf0419Mult : Fin 44 → Nat := ![10127, 28609, 17555, 6929, 11844, 5938, 9010, 15922, 6216, 11070, 14208, 27500, 6178, 5634, 1392, 4534, 10374, 2302, 6886, 2304, 8144, 11734, 1628, 708, 12094, 10858, 82, 3090, 15756, 28436, 13430, 55936, 4582, 496, 34242, 35544, 146040, 13180, 91634, 56368, 55228, 53634, 38458, 93222]

theorem plane484GenLeaf0419 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0419Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0419Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0419Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0419Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 307
  · exact hroot.hOcc 474
  · exact hroot.hOcc 506
  · exact hroot.hOcc 838
  · exact hroot.hOcc 841
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1302
  · exact hroot.hOcc 1320
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1507
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
