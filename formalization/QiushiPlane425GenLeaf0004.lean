import QiushiPlane425GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane425GenLeaf0004Refs : Fin 59 → RowRef 202 58 := ![.occ 5, .occ 6, .occ 7, .occ 11, .occ 17, .occ 18, .occ 19, .occ 23, .occ 42, .occ 54, .occ 62, .occ 69, .occ 76, .occ 79, .occ 83, .occ 91, .occ 94, .occ 103, .occ 110, .occ 112, .occ 120, .occ 122, .occ 136, .occ 139, .occ 141, .occ 147, .occ 151, .occ 157, .occ 160, .occ 161, .occ 162, .occ 163, .occ 168, .occ 169, .occ 170, .occ 179, .occ 187, .occ 188, .occ 190, .occ 192, .occ 195, .occ 196, .occ 198, .sumGe, .nonneg 2, .nonneg 14, .nonneg 22, .nonneg 23, .nonneg 24, .nonneg 35, .nonneg 38, .nonneg 45, .nonneg 52, .nonneg 55, .branchGe 17 (1), .branchLe 9 (0), .branchLe 43 (0), .branchLe 20 (0), .branchGe 6 (1)]

def plane425GenLeaf0004Mult : Fin 59 → Nat := ![30300, 3552, 21700, 1406, 326, 4468, 20296, 16032, 6412, 25428, 11802, 6264, 11502, 10452, 1840, 4378, 5780, 4322, 12434, 7710, 2275, 817, 8758, 11358, 9308, 8, 15286, 1688, 2490, 19, 6441, 2336, 4174, 2957, 2091, 13398, 1534, 2080, 6853, 48, 6428, 9184, 9357, 41980, 11438, 18190, 1772, 28930, 17542, 5320, 10048, 5642, 444, 17202, 93448, 484, 26484, 35552, 185682]

theorem plane425GenLeaf0004 (x : Fin 58 → Int)
    (hroot : plane425GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane425GenLeaf0004Refs i).resolveCoeff plane425GenOccSys j)
    (fun i => (plane425GenLeaf0004Refs i).resolveRhs plane425GenOccSys) plane425GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane425GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 11
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 23
  · exact hroot.hOcc 42
  · exact hroot.hOcc 54
  · exact hroot.hOcc 62
  · exact hroot.hOcc 69
  · exact hroot.hOcc 76
  · exact hroot.hOcc 79
  · exact hroot.hOcc 83
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 103
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 147
  · exact hroot.hOcc 151
  · exact hroot.hOcc 157
  · exact hroot.hOcc 160
  · exact hroot.hOcc 161
  · exact hroot.hOcc 162
  · exact hroot.hOcc 163
  · exact hroot.hOcc 168
  · exact hroot.hOcc 169
  · exact hroot.hOcc 170
  · exact hroot.hOcc 179
  · exact hroot.hOcc 187
  · exact hroot.hOcc 188
  · exact hroot.hOcc 190
  · exact hroot.hOcc 192
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 198
  · change (∑ j, (-1 : Int) * x j) ≤ -plane425GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (22 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (35 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (38 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (45 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (52 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (55 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (9 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (20 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (6 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
