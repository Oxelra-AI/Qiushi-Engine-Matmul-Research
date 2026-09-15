import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0395Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 124, .occ 125, .occ 126, .occ 127, .occ 137, .occ 141, .occ 173, .occ 507, .occ 614, .occ 838, .occ 860, .occ 1136, .occ 1145, .occ 1166, .occ 1172, .occ 1196, .occ 1208, .occ 1237, .occ 1381, .occ 1408, .occ 1470, .occ 1488, .occ 1525, .occ 1533, .occ 1545, .occ 1567, .occ 1607, .occ 1629, .occ 1633, .occ 1636, .sumGe, .nonneg 10, .nonneg 11, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchLe 31 (0), .branchLe 24 (0), .branchLe 37 (0), .branchLe 35 (0), .branchGe 33 (1)]

def plane484GenLeaf0395Mult : Fin 44 → Nat := ![2174, 7214, 454, 223, 2293, 3444, 835, 2338, 2903, 1004, 5780, 407, 118, 27, 146, 4242, 1469, 5585, 652, 219, 591, 3265, 1110, 1401, 113, 1140, 3590, 310, 2684, 396, 830, 2657, 12934, 391, 110, 11708, 7580, 31823, 3102, 12934, 2766, 12788, 6838, 11198]

theorem plane484GenLeaf0395 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0395Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0395Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0395Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0395Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 173
  · exact hroot.hOcc 507
  · exact hroot.hOcc 614
  · exact hroot.hOcc 838
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1237
  · exact hroot.hOcc 1381
  · exact hroot.hOcc 1408
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1525
  · exact hroot.hOcc 1533
  · exact hroot.hOcc 1545
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1633
  · exact hroot.hOcc 1636
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
