import QiushiPlane470GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane470GenLeaf0000Refs : Fin 64 → RowRef 232 63 := ![.occ 25, .occ 34, .occ 36, .occ 38, .occ 40, .occ 45, .occ 62, .occ 63, .occ 67, .occ 68, .occ 69, .occ 72, .occ 74, .occ 80, .occ 84, .occ 88, .occ 89, .occ 103, .occ 104, .occ 106, .occ 110, .occ 111, .occ 112, .occ 115, .occ 119, .occ 125, .occ 126, .occ 128, .occ 141, .occ 142, .occ 143, .occ 146, .occ 155, .occ 156, .occ 157, .occ 161, .occ 171, .occ 172, .occ 173, .occ 174, .occ 175, .occ 177, .occ 194, .occ 196, .occ 198, .occ 203, .occ 216, .occ 217, .occ 218, .occ 220, .occ 222, .occ 228, .occ 230, .sumGe, .nonneg 10, .nonneg 32, .nonneg 55, .nonneg 59, .branchLe 12 (0), .branchLe 60 (0), .branchLe 25 (0), .branchLe 15 (0), .branchLe 4 (0), .branchLe 9 (0)]

def plane470GenLeaf0000Mult : Fin 64 → Nat := ![1181845230, 87999622, 936938666, 927014528, 584720778, 301353678, 636142542, 1058870372, 151276034, 850060962, 120338856, 970158896, 530229832, 2510476302, 1690021462, 2543494256, 370529976, 2555630450, 559595054, 810102498, 831530738, 1196559596, 623491320, 788438958, 294625694, 37578190, 1166218064, 246590670, 1275866988, 941853948, 1192931684, 579012628, 1309211904, 192715156, 1380918554, 462097886, 1283930558, 1661616828, 541196364, 467541404, 172857348, 207357492, 554550598, 719684802, 383001636, 364879800, 669093316, 197708432, 1289424063, 301428270, 310778135, 546537991, 83632335, 7289354438, 580816170, 673265366, 3251416730, 241456152, 543202718, 4254771148, 5689152240, 4438018538, 5738011534, 6620261122]

theorem plane470GenLeaf0000 (x : Fin 63 → Int)
    (hroot : plane470GenOccSys.RootHolds x)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane470GenLeaf0000Refs i).resolveCoeff plane470GenOccSys j)
    (fun i => (plane470GenLeaf0000Refs i).resolveRhs plane470GenOccSys) plane470GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane470GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 25
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 38
  · exact hroot.hOcc 40
  · exact hroot.hOcc 45
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 72
  · exact hroot.hOcc 74
  · exact hroot.hOcc 80
  · exact hroot.hOcc 84
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 115
  · exact hroot.hOcc 119
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 146
  · exact hroot.hOcc 155
  · exact hroot.hOcc 156
  · exact hroot.hOcc 157
  · exact hroot.hOcc 161
  · exact hroot.hOcc 171
  · exact hroot.hOcc 172
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 177
  · exact hroot.hOcc 194
  · exact hroot.hOcc 196
  · exact hroot.hOcc 198
  · exact hroot.hOcc 203
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · exact hroot.hOcc 218
  · exact hroot.hOcc 220
  · exact hroot.hOcc 222
  · exact hroot.hOcc 228
  · exact hroot.hOcc 230
  · change (∑ j, (-1 : Int) * x j) ≤ -plane470GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (12 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (60 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (25 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (15 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (4 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (9 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
