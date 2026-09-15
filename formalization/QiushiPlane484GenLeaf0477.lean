import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0477Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 123, .occ 127, .occ 138, .occ 142, .occ 271, .occ 330, .occ 377, .occ 378, .occ 416, .occ 1008, .occ 1011, .occ 1146, .occ 1151, .occ 1158, .occ 1172, .occ 1186, .occ 1310, .occ 1329, .occ 1339, .occ 1453, .occ 1484, .occ 1567, .occ 1590, .occ 1603, .occ 1609, .occ 1610, .occ 1637, .sumGe, .nonneg 5, .nonneg 11, .nonneg 26, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 19 (0), .branchLe 25 (0), .branchLe 3 (0), .branchGe 38 (1), .branchLe 34 (0), .branchGe 6 (1)]

def plane484GenLeaf0477Mult : Fin 43 → Nat := ![148, 195, 167, 64, 22, 94, 148, 234, 183, 99, 11, 84, 234, 150, 135, 51, 27, 7, 21, 50, 25, 12, 25, 35, 20, 10, 167, 192, 8, 414, 177, 44, 106, 748, 338, 96, 509, 8, 320, 76, 925, 414, 1664]

theorem plane484GenLeaf0477 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0477Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0477Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0477Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0477Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 127
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 271
  · exact hroot.hOcc 330
  · exact hroot.hOcc 377
  · exact hroot.hOcc 378
  · exact hroot.hOcc 416
  · exact hroot.hOcc 1008
  · exact hroot.hOcc 1011
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1310
  · exact hroot.hOcc 1329
  · exact hroot.hOcc 1339
  · exact hroot.hOcc 1453
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1637
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
