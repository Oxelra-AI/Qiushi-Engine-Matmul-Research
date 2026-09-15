import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0206Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 127, .occ 130, .occ 132, .occ 141, .occ 196, .occ 201, .occ 214, .occ 267, .occ 307, .occ 329, .occ 366, .occ 437, .occ 473, .occ 550, .occ 614, .occ 1140, .occ 1151, .occ 1170, .occ 1179, .occ 1214, .occ 1216, .occ 1220, .occ 1259, .occ 1357, .occ 1472, .occ 1478, .occ 1486, .occ 1499, .occ 1555, .occ 1601, .sumGe, .nonneg 20, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchGe 1 (1), .branchGe 22 (1), .branchGe 0 (1), .branchLe 8 (0), .branchGe 19 (1)]

def plane484GenLeaf0206Mult : Fin 44 → Nat := ![398, 1294, 60, 363, 626, 640, 396, 286, 530, 359, 882, 2, 342, 682, 112, 314, 652, 316, 249, 167, 1269, 194, 194, 117, 356, 739, 102, 891, 192, 211, 570, 2302, 91, 1207, 1097, 4830, 4357, 1986, 1121, 3119, 1107, 710, 2302, 3883]

theorem plane484GenLeaf0206 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0206Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0206Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0206Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0206Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 141
  · exact hroot.hOcc 196
  · exact hroot.hOcc 201
  · exact hroot.hOcc 214
  · exact hroot.hOcc 267
  · exact hroot.hOcc 307
  · exact hroot.hOcc 329
  · exact hroot.hOcc 366
  · exact hroot.hOcc 437
  · exact hroot.hOcc 473
  · exact hroot.hOcc 550
  · exact hroot.hOcc 614
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1499
  · exact hroot.hOcc 1555
  · exact hroot.hOcc 1601
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19

end QiushiMatmul
