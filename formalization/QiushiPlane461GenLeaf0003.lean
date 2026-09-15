import QiushiPlane461GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane461GenLeaf0003Refs : Fin 63 → RowRef 151 62 := ![.occ 16, .occ 19, .occ 23, .occ 25, .occ 28, .occ 30, .occ 33, .occ 34, .occ 36, .occ 37, .occ 39, .occ 40, .occ 44, .occ 45, .occ 46, .occ 47, .occ 54, .occ 61, .occ 63, .occ 65, .occ 67, .occ 68, .occ 74, .occ 76, .occ 78, .occ 80, .occ 81, .occ 83, .occ 87, .occ 88, .occ 89, .occ 91, .occ 93, .occ 95, .occ 98, .occ 105, .occ 111, .occ 113, .occ 122, .occ 123, .occ 129, .occ 136, .occ 139, .occ 142, .occ 146, .sumGe, .nonneg 6, .nonneg 9, .nonneg 11, .nonneg 12, .nonneg 32, .nonneg 33, .nonneg 35, .nonneg 36, .nonneg 38, .nonneg 39, .nonneg 44, .nonneg 51, .nonneg 54, .nonneg 57, .branchGe 16 (1), .branchLe 48 (0), .branchLe 21 (0)]

def plane461GenLeaf0003Mult : Fin 63 → Nat := ![2353702, 33712, 511702, 100594, 1115724, 2945137, 1933960, 1600120, 516442, 904801, 636728, 106627, 319714, 1239821, 13460, 1395910, 330309, 1029024, 245342, 555844, 448935, 263653, 212473, 616383, 133799, 10463, 1123044, 420286, 1258290, 1607848, 1347019, 117690, 578824, 1327587, 425030, 447731, 384792, 157520, 68915, 136912, 47985, 210785, 162800, 94581, 126984, 3698234, 3284328, 3937086, 323762, 957030, 1140128, 2771194, 774730, 1774068, 1772826, 1652710, 2035882, 1837102, 736962, 860346, 6746444, 3417744, 3698234]

theorem plane461GenLeaf0003 (x : Fin 62 → Int)
    (hroot : plane461GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane461GenLeaf0003Refs i).resolveCoeff plane461GenOccSys j)
    (fun i => (plane461GenLeaf0003Refs i).resolveRhs plane461GenOccSys) plane461GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane461GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 16
  · exact hroot.hOcc 19
  · exact hroot.hOcc 23
  · exact hroot.hOcc 25
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 54
  · exact hroot.hOcc 61
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 83
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 98
  · exact hroot.hOcc 105
  · exact hroot.hOcc 111
  · exact hroot.hOcc 113
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 142
  · exact hroot.hOcc 146
  · change (∑ j, (-1 : Int) * x j) ≤ -plane461GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (9 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (11 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (12 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (35 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (36 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (38 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (44 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (54 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (16 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (48 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (21 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21

end QiushiMatmul
