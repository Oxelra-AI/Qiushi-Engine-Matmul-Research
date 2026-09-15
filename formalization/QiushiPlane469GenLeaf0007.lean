import QiushiPlane469GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane469GenLeaf0007Refs : Fin 61 → RowRef 217 60 := ![.occ 5, .occ 7, .occ 10, .occ 14, .occ 19, .occ 20, .occ 29, .occ 31, .occ 34, .occ 54, .occ 56, .occ 57, .occ 58, .occ 60, .occ 62, .occ 68, .occ 69, .occ 76, .occ 83, .occ 84, .occ 87, .occ 88, .occ 93, .occ 95, .occ 97, .occ 104, .occ 107, .occ 110, .occ 122, .occ 127, .occ 128, .occ 134, .occ 136, .occ 139, .occ 143, .occ 144, .occ 148, .occ 158, .occ 168, .occ 174, .occ 179, .occ 198, .occ 204, .occ 205, .occ 208, .occ 211, .occ 212, .occ 214, .occ 215, .sumGe, .nonneg 7, .nonneg 10, .nonneg 17, .nonneg 19, .nonneg 25, .nonneg 32, .nonneg 46, .nonneg 57, .nonneg 59, .branchLe 34 (0), .branchGe 13 (1)]

def plane469GenLeaf0007Mult : Fin 61 → Nat := ![193173792, 24367108, 61417472, 16928772, 16295524, 9210884, 31463124, 61887344, 164581132, 106003312, 33294828, 36918648, 91265496, 146981152, 48601704, 190156684, 35738816, 30724604, 46542744, 116455080, 11437964, 5089368, 45990024, 23213212, 47717844, 10517164, 53525572, 43931064, 52139478, 4070800, 37556722, 11510240, 4107152, 37905468, 32976638, 4237476, 12509188, 352844, 27085744, 86910212, 120427296, 31210382, 8708974, 5541746, 92995242, 51323237, 12089567, 22504601, 788367, 320070574, 3665300, 66285744, 64611940, 51107392, 42019676, 129247056, 322845428, 35515204, 12815768, 295401832, 1086293932]

theorem plane469GenLeaf0007 (x : Fin 60 → Int)
    (hroot : plane469GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane469GenLeaf0007Refs i).resolveCoeff plane469GenOccSys j)
    (fun i => (plane469GenLeaf0007Refs i).resolveRhs plane469GenOccSys) plane469GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane469GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 7
  · exact hroot.hOcc 10
  · exact hroot.hOcc 14
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 29
  · exact hroot.hOcc 31
  · exact hroot.hOcc 34
  · exact hroot.hOcc 54
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 60
  · exact hroot.hOcc 62
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 76
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 104
  · exact hroot.hOcc 107
  · exact hroot.hOcc 110
  · exact hroot.hOcc 122
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 143
  · exact hroot.hOcc 144
  · exact hroot.hOcc 148
  · exact hroot.hOcc 158
  · exact hroot.hOcc 168
  · exact hroot.hOcc 174
  · exact hroot.hOcc 179
  · exact hroot.hOcc 198
  · exact hroot.hOcc 204
  · exact hroot.hOcc 205
  · exact hroot.hOcc 208
  · exact hroot.hOcc 211
  · exact hroot.hOcc 212
  · exact hroot.hOcc 214
  · exact hroot.hOcc 215
  · change (∑ j, (-1 : Int) * x j) ≤ -plane469GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (10 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (17 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (25 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (32 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (46 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (57 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (59 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (34 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 60) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
