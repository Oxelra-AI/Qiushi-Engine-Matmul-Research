import QiushiPlane472GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane472GenLeaf0009Refs : Fin 63 → RowRef 242 62 := ![.occ 3, .occ 5, .occ 13, .occ 34, .occ 44, .occ 45, .occ 51, .occ 52, .occ 53, .occ 54, .occ 65, .occ 75, .occ 76, .occ 84, .occ 85, .occ 87, .occ 94, .occ 109, .occ 112, .occ 114, .occ 115, .occ 121, .occ 129, .occ 130, .occ 132, .occ 138, .occ 139, .occ 143, .occ 146, .occ 168, .occ 174, .occ 175, .occ 176, .occ 181, .occ 183, .occ 187, .occ 188, .occ 191, .occ 192, .occ 193, .occ 194, .occ 196, .occ 230, .occ 231, .occ 239, .occ 240, .occ 241, .sumGe, .nonneg 0, .nonneg 7, .nonneg 10, .nonneg 18, .nonneg 24, .nonneg 27, .nonneg 32, .nonneg 36, .nonneg 40, .nonneg 42, .nonneg 57, .nonneg 61, .branchGe 60 (1), .branchLe 6 (0), .branchLe 5 (0)]

def plane472GenLeaf0009Mult : Fin 63 → Nat := ![410052, 2229002, 180086, 598764, 1866534, 105932, 5898798, 3966354, 4292574, 5398556, 536814, 1726550, 183088, 1356118, 1244772, 2431270, 2296848, 3034066, 5571618, 2278850, 2470670, 4313978, 178756, 231714, 45113, 91690, 1966626, 109040, 2115780, 2061486, 1076263, 820014, 1438769, 735007, 9490, 142978, 541434, 988023, 185156, 1465220, 1557942, 2717761, 257542, 373424, 502177, 1796957, 1013022, 9359858, 1057154, 2415712, 911704, 4455952, 1477526, 2325962, 2771982, 278342, 1459142, 4323334, 2559470, 3015796, 36882542, 5396532, 8986434]

theorem plane472GenLeaf0009 (x : Fin 62 → Int)
    (hroot : plane472GenOccSys.RootHolds x)
    (hLB_60 : (1 : Int) ≤ x 60)
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane472GenLeaf0009Refs i).resolveCoeff plane472GenOccSys j)
    (fun i => (plane472GenLeaf0009Refs i).resolveRhs plane472GenOccSys) plane472GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane472GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 5
  · exact hroot.hOcc 13
  · exact hroot.hOcc 34
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 54
  · exact hroot.hOcc 65
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 87
  · exact hroot.hOcc 94
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 121
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 143
  · exact hroot.hOcc 146
  · exact hroot.hOcc 168
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 181
  · exact hroot.hOcc 183
  · exact hroot.hOcc 187
  · exact hroot.hOcc 188
  · exact hroot.hOcc 191
  · exact hroot.hOcc 192
  · exact hroot.hOcc 193
  · exact hroot.hOcc 194
  · exact hroot.hOcc 196
  · exact hroot.hOcc 230
  · exact hroot.hOcc 231
  · exact hroot.hOcc 239
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · change (∑ j, (-1 : Int) * x j) ≤ -plane472GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (18 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (24 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (27 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (36 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (42 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (61 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (60 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_60
  · change (∑ k, (if k = (6 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (5 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5

end QiushiMatmul
