import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0102Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 120, .occ 124, .occ 127, .occ 134, .occ 137, .occ 139, .occ 142, .occ 174, .occ 282, .occ 407, .occ 415, .occ 807, .occ 855, .occ 856, .occ 992, .occ 994, .occ 1080, .occ 1086, .occ 1146, .occ 1234, .occ 1254, .occ 1261, .occ 1323, .occ 1357, .occ 1384, .occ 1395, .occ 1580, .occ 1609, .occ 1628, .occ 1639, .sumGe, .nonneg 20, .nonneg 21, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchGe 26 (1), .branchGe 37 (1), .branchLe 34 (0), .branchGe 16 (1)]

def plane484GenLeaf0102Mult : Fin 43 → Nat := ![53, 23, 37, 80, 21, 41, 144, 196, 43, 204, 9, 17, 147, 60, 135, 14, 67, 78, 78, 60, 9, 154, 27, 32, 24, 52, 41, 24, 29, 56, 101, 325, 70, 222, 129, 86, 325, 736, 301, 577, 865, 325, 882]

theorem plane484GenLeaf0102 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0102Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0102Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0102Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0102Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 127
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 142
  · exact hroot.hOcc 174
  · exact hroot.hOcc 282
  · exact hroot.hOcc 407
  · exact hroot.hOcc 415
  · exact hroot.hOcc 807
  · exact hroot.hOcc 855
  · exact hroot.hOcc 856
  · exact hroot.hOcc 992
  · exact hroot.hOcc 994
  · exact hroot.hOcc 1080
  · exact hroot.hOcc 1086
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1254
  · exact hroot.hOcc 1261
  · exact hroot.hOcc 1323
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1395
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1639
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
