import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0048Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 128, .occ 132, .occ 133, .occ 139, .occ 140, .occ 433, .occ 519, .occ 830, .occ 834, .occ 846, .occ 847, .occ 984, .occ 1061, .occ 1136, .occ 1174, .occ 1190, .occ 1213, .occ 1220, .occ 1244, .occ 1338, .occ 1470, .occ 1509, .occ 1518, .occ 1524, .occ 1553, .occ 1567, .occ 1580, .occ 1610, .sumGe, .nonneg 5, .nonneg 10, .nonneg 15, .nonneg 18, .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchGe 17 (1), .branchLe 7 (0), .branchGe 1 (1), .branchGe 38 (1), .branchLe 35 (0)]

def plane484GenLeaf0048Mult : Fin 43 → Nat := ![42, 611, 378, 880, 36, 1145, 469, 128, 941, 656, 262, 8, 351, 243, 97, 200, 169, 36, 236, 236, 114, 753, 18, 67, 117, 540, 237, 200, 1006, 1759, 42, 145, 266, 711, 1353, 1425, 1384, 1590, 5939, 1499, 2102, 3597, 1487]

theorem plane484GenLeaf0048 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0048Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0048Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0048Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0048Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 433
  · exact hroot.hOcc 519
  · exact hroot.hOcc 830
  · exact hroot.hOcc 834
  · exact hroot.hOcc 846
  · exact hroot.hOcc 847
  · exact hroot.hOcc 984
  · exact hroot.hOcc 1061
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1244
  · exact hroot.hOcc 1338
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1509
  · exact hroot.hOcc 1518
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1553
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1610
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35

end QiushiMatmul
