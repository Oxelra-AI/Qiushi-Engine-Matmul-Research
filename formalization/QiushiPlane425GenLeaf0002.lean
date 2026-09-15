import QiushiPlane425GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane425GenLeaf0002Refs : Fin 59 → RowRef 202 58 := ![.occ 6, .occ 9, .occ 10, .occ 14, .occ 22, .occ 24, .occ 46, .occ 53, .occ 58, .occ 63, .occ 66, .occ 71, .occ 73, .occ 84, .occ 90, .occ 92, .occ 94, .occ 114, .occ 116, .occ 118, .occ 121, .occ 123, .occ 128, .occ 153, .occ 154, .occ 156, .occ 157, .occ 159, .occ 163, .occ 164, .occ 166, .occ 173, .occ 178, .occ 184, .occ 185, .occ 189, .occ 191, .occ 192, .occ 194, .occ 198, .occ 199, .sumGe, .nonneg 2, .nonneg 3, .nonneg 13, .nonneg 14, .nonneg 15, .nonneg 19, .nonneg 23, .nonneg 32, .nonneg 33, .nonneg 36, .nonneg 41, .nonneg 45, .nonneg 48, .nonneg 55, .nonneg 56, .branchLe 17 (0), .branchGe 8 (1)]

def plane425GenLeaf0002Mult : Fin 59 → Nat := ![24132, 4370, 28256, 4370, 23442, 4660, 29072, 15404, 10482, 8110, 15942, 7060, 650, 3284, 11942, 17458, 12412, 8867, 12319, 4801, 305, 10464, 2523, 3060, 1309, 702, 15847, 6915, 2323, 2978, 12342, 12232, 558, 5068, 23897, 1765, 13588, 17700, 1695, 29535, 22721, 83544, 54966, 48930, 63756, 34090, 77200, 24420, 11836, 24078, 1926, 3612, 37796, 14450, 19584, 8344, 26974, 80484, 135654]

theorem plane425GenLeaf0002 (x : Fin 58 → Int)
    (hroot : plane425GenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_17 : x 17 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane425GenLeaf0002Refs i).resolveCoeff plane425GenOccSys j)
    (fun i => (plane425GenLeaf0002Refs i).resolveRhs plane425GenOccSys) plane425GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane425GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 14
  · exact hroot.hOcc 22
  · exact hroot.hOcc 24
  · exact hroot.hOcc 46
  · exact hroot.hOcc 53
  · exact hroot.hOcc 58
  · exact hroot.hOcc 63
  · exact hroot.hOcc 66
  · exact hroot.hOcc 71
  · exact hroot.hOcc 73
  · exact hroot.hOcc 84
  · exact hroot.hOcc 90
  · exact hroot.hOcc 92
  · exact hroot.hOcc 94
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 153
  · exact hroot.hOcc 154
  · exact hroot.hOcc 156
  · exact hroot.hOcc 157
  · exact hroot.hOcc 159
  · exact hroot.hOcc 163
  · exact hroot.hOcc 164
  · exact hroot.hOcc 166
  · exact hroot.hOcc 173
  · exact hroot.hOcc 178
  · exact hroot.hOcc 184
  · exact hroot.hOcc 185
  · exact hroot.hOcc 189
  · exact hroot.hOcc 191
  · exact hroot.hOcc 192
  · exact hroot.hOcc 194
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · change (∑ j, (-1 : Int) * x j) ≤ -plane425GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (3 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (13 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (32 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (41 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (45 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (48 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (55 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (56 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (17 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (8 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
