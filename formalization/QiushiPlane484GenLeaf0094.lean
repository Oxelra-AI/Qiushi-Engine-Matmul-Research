import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0094Refs : Fin 42 → RowRef 1665 43 := ![.occ 119, .occ 127, .occ 129, .occ 130, .occ 139, .occ 140, .occ 141, .occ 142, .occ 338, .occ 413, .occ 423, .occ 424, .occ 652, .occ 792, .occ 809, .occ 855, .occ 995, .occ 1150, .occ 1242, .occ 1256, .occ 1385, .occ 1435, .occ 1442, .occ 1449, .occ 1450, .occ 1477, .occ 1573, .occ 1626, .occ 1627, .occ 1659, .sumGe, .nonneg 0, .nonneg 1, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchGe 26 (1), .branchLe 37 (0), .branchLe 28 (0), .branchLe 38 (0)]

def plane484GenLeaf0094Mult : Fin 42 → Nat := ![2401, 2080, 1035, 2616, 3382, 1778, 1566, 646, 812, 919, 2099, 641, 225, 499, 995, 343, 313, 23, 1225, 310, 196, 433, 1435, 547, 523, 737, 2966, 669, 98, 464, 5927, 3470, 2171, 1520, 2961, 5927, 13985, 2126, 8390, 5904, 5927, 5927]

theorem plane484GenLeaf0094 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0094Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0094Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0094Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0094Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 338
  · exact hroot.hOcc 413
  · exact hroot.hOcc 423
  · exact hroot.hOcc 424
  · exact hroot.hOcc 652
  · exact hroot.hOcc 792
  · exact hroot.hOcc 809
  · exact hroot.hOcc 855
  · exact hroot.hOcc 995
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1242
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1435
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1450
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1627
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38

end QiushiMatmul
