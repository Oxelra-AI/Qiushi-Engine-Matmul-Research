import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0082Refs : Fin 42 → RowRef 1665 43 := ![.occ 123, .occ 129, .occ 131, .occ 135, .occ 141, .occ 144, .occ 492, .occ 534, .occ 581, .occ 802, .occ 804, .occ 805, .occ 1005, .occ 1007, .occ 1050, .occ 1053, .occ 1170, .occ 1172, .occ 1173, .occ 1305, .occ 1321, .occ 1343, .occ 1375, .occ 1403, .occ 1418, .occ 1424, .occ 1429, .occ 1602, .sumGe, .nonneg 1, .nonneg 2, .nonneg 9, .nonneg 15, .nonneg 16, .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchGe 42 (1), .branchGe 20 (1), .branchGe 41 (1), .branchGe 24 (1), .branchGe 3 (1)]

def plane484GenLeaf0082Mult : Fin 42 → Nat := ![83, 11, 73, 84, 10, 77, 39, 6, 82, 22, 96, 148, 74, 28, 2, 21, 11, 6, 5, 1, 56, 39, 21, 54, 94, 20, 32, 32, 148, 11, 19, 190, 246, 53, 148, 148, 304, 394, 502, 132, 564, 606]

theorem plane484GenLeaf0082 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0082Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0082Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0082Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0082Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 135
  · exact hroot.hOcc 141
  · exact hroot.hOcc 144
  · exact hroot.hOcc 492
  · exact hroot.hOcc 534
  · exact hroot.hOcc 581
  · exact hroot.hOcc 802
  · exact hroot.hOcc 804
  · exact hroot.hOcc 805
  · exact hroot.hOcc 1005
  · exact hroot.hOcc 1007
  · exact hroot.hOcc 1050
  · exact hroot.hOcc 1053
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1305
  · exact hroot.hOcc 1321
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1375
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1418
  · exact hroot.hOcc 1424
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1602
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
