import QiushiPlane456GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane456GenLeaf0007Refs : Fin 64 → RowRef 248 63 := ![.occ 17, .occ 22, .occ 24, .occ 36, .occ 37, .occ 39, .occ 47, .occ 54, .occ 55, .occ 61, .occ 62, .occ 63, .occ 64, .occ 65, .occ 81, .occ 82, .occ 83, .occ 90, .occ 106, .occ 107, .occ 111, .occ 112, .occ 124, .occ 129, .occ 130, .occ 131, .occ 132, .occ 133, .occ 134, .occ 135, .occ 139, .occ 140, .occ 148, .occ 149, .occ 151, .occ 154, .occ 157, .occ 161, .occ 162, .occ 164, .occ 176, .occ 178, .occ 182, .occ 186, .occ 200, .occ 203, .occ 208, .occ 212, .occ 218, .occ 228, .occ 235, .occ 238, .sumGe, .nonneg 21, .nonneg 28, .nonneg 32, .nonneg 41, .nonneg 42, .nonneg 44, .nonneg 60, .branchLe 24 (0), .branchLe 31 (0), .branchGe 57 (1), .branchGe 61 (1)]

def plane456GenLeaf0007Mult : Fin 64 → Nat := ![23716, 190168, 28932, 158120, 524, 69928, 93706, 2936, 119300, 381194, 210070, 76538, 123276, 259756, 39894, 67494, 25612, 121408, 20249, 69, 153626, 160931, 12340, 165686, 105240, 354374, 45914, 185156, 22622, 37070, 71558, 318164, 129364, 3242, 42387, 73351, 55887, 16722, 266, 11391, 71615, 13730, 8723, 40749, 219763, 105370, 123714, 15879, 133453, 22030, 5941, 10330, 459744, 84064, 264652, 145838, 51734, 88166, 49460, 95622, 325670, 358520, 1187930, 1988550]

theorem plane456GenLeaf0007 (x : Fin 63 → Int)
    (hroot : plane456GenOccSys.RootHolds x)
    (hLB_57 : (1 : Int) ≤ x 57)
    (hLB_61 : (1 : Int) ≤ x 61)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane456GenLeaf0007Refs i).resolveCoeff plane456GenOccSys j)
    (fun i => (plane456GenLeaf0007Refs i).resolveRhs plane456GenOccSys) plane456GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane456GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 17
  · exact hroot.hOcc 22
  · exact hroot.hOcc 24
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 39
  · exact hroot.hOcc 47
  · exact hroot.hOcc 54
  · exact hroot.hOcc 55
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 90
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 148
  · exact hroot.hOcc 149
  · exact hroot.hOcc 151
  · exact hroot.hOcc 154
  · exact hroot.hOcc 157
  · exact hroot.hOcc 161
  · exact hroot.hOcc 162
  · exact hroot.hOcc 164
  · exact hroot.hOcc 176
  · exact hroot.hOcc 178
  · exact hroot.hOcc 182
  · exact hroot.hOcc 186
  · exact hroot.hOcc 200
  · exact hroot.hOcc 203
  · exact hroot.hOcc 208
  · exact hroot.hOcc 212
  · exact hroot.hOcc 218
  · exact hroot.hOcc 228
  · exact hroot.hOcc 235
  · exact hroot.hOcc 238
  · change (∑ j, (-1 : Int) * x j) ≤ -plane456GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (28 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (41 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (60 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (31 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (57 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_57
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_61

end QiushiMatmul
