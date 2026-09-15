import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0402Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 129, .occ 130, .occ 132, .occ 137, .occ 141, .occ 143, .occ 442, .occ 508, .occ 509, .occ 639, .occ 1119, .occ 1164, .occ 1168, .occ 1174, .occ 1183, .occ 1191, .occ 1208, .occ 1353, .occ 1370, .occ 1405, .occ 1419, .occ 1484, .occ 1486, .occ 1489, .occ 1532, .occ 1571, .occ 1608, .occ 1639, .occ 1653, .sumGe, .nonneg 4, .nonneg 10, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchLe 31 (0), .branchLe 24 (0), .branchGe 37 (1), .branchGe 0 (1), .branchLe 5 (0), .branchLe 1 (0), .branchLe 33 (0)]

def plane484GenLeaf0402Mult : Fin 44 → Nat := ![12976, 4050, 8530, 2554, 14704, 3176, 13772, 11036, 1036, 6494, 1994, 8898, 588, 2087, 7002, 6361, 520, 3868, 5502, 260, 242, 500, 1966, 17914, 2353, 11314, 3132, 12543, 3268, 5916, 35778, 3810, 24916, 33812, 37110, 91364, 11798, 16874, 32636, 56616, 16228, 7988, 18992, 35778]

theorem plane484GenLeaf0402 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0402Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0402Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0402Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0402Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 442
  · exact hroot.hOcc 508
  · exact hroot.hOcc 509
  · exact hroot.hOcc 639
  · exact hroot.hOcc 1119
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1370
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1419
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1532
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33

end QiushiMatmul
