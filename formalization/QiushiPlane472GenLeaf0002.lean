import QiushiPlane472GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane472GenLeaf0002Refs : Fin 63 → RowRef 242 62 := ![.occ 1, .occ 4, .occ 15, .occ 21, .occ 22, .occ 24, .occ 25, .occ 34, .occ 41, .occ 44, .occ 45, .occ 47, .occ 49, .occ 64, .occ 65, .occ 69, .occ 75, .occ 76, .occ 81, .occ 88, .occ 91, .occ 92, .occ 94, .occ 95, .occ 102, .occ 105, .occ 116, .occ 118, .occ 123, .occ 132, .occ 148, .occ 149, .occ 153, .occ 157, .occ 164, .occ 165, .occ 168, .occ 174, .occ 175, .occ 176, .occ 179, .occ 196, .occ 209, .occ 217, .occ 218, .occ 227, .occ 228, .occ 231, .occ 234, .sumGe, .nonneg 3, .nonneg 10, .nonneg 16, .nonneg 22, .nonneg 40, .nonneg 45, .nonneg 49, .nonneg 54, .branchLe 60 (0), .branchLe 4 (0), .branchLe 33 (0), .branchLe 11 (0), .branchGe 21 (1)]

def plane472GenLeaf0002Mult : Fin 63 → Nat := ![530465, 2755198, 1150671, 256038, 1762119, 201642, 857380, 1178100, 1630590, 378820, 140466, 639512, 44306, 1110461, 1639492, 332282, 481638, 230943, 961021, 226493, 579526, 96119, 1152806, 211965, 961627, 730153, 961144, 235357, 187784, 425146, 281227, 352315, 290622, 274066, 124667, 329171, 205170, 481204, 1779063, 579085, 390537, 197374, 531094, 206282, 691658, 604927, 148575, 332639, 367842, 3917541, 550678, 56449, 3070, 242917, 2389190, 1528640, 550375, 20396, 3387528, 1671344, 3351831, 2957757, 13094254]

theorem plane472GenLeaf0002 (x : Fin 62 → Int)
    (hroot : plane472GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane472GenLeaf0002Refs i).resolveCoeff plane472GenOccSys j)
    (fun i => (plane472GenLeaf0002Refs i).resolveRhs plane472GenOccSys) plane472GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane472GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 4
  · exact hroot.hOcc 15
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 34
  · exact hroot.hOcc 41
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 47
  · exact hroot.hOcc 49
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 69
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 81
  · exact hroot.hOcc 88
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 123
  · exact hroot.hOcc 132
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 153
  · exact hroot.hOcc 157
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 168
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 179
  · exact hroot.hOcc 196
  · exact hroot.hOcc 209
  · exact hroot.hOcc 217
  · exact hroot.hOcc 218
  · exact hroot.hOcc 227
  · exact hroot.hOcc 228
  · exact hroot.hOcc 231
  · exact hroot.hOcc 234
  · change (∑ j, (-1 : Int) * x j) ≤ -plane472GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (16 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (22 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (45 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (49 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (54 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (60 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (4 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (33 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (11 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (21 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
