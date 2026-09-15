import QiushiPlane458GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane458GenLeaf0002Refs : Fin 57 → RowRef 203 56 := ![.occ 8, .occ 16, .occ 21, .occ 27, .occ 34, .occ 36, .occ 39, .occ 46, .occ 47, .occ 49, .occ 52, .occ 54, .occ 60, .occ 67, .occ 70, .occ 74, .occ 75, .occ 76, .occ 78, .occ 81, .occ 84, .occ 88, .occ 90, .occ 95, .occ 98, .occ 106, .occ 109, .occ 111, .occ 114, .occ 123, .occ 133, .occ 135, .occ 142, .occ 144, .occ 149, .occ 151, .occ 161, .occ 167, .occ 168, .occ 176, .occ 189, .occ 195, .occ 197, .occ 202, .sumGe, .nonneg 6, .nonneg 13, .nonneg 25, .nonneg 29, .nonneg 32, .nonneg 37, .nonneg 43, .nonneg 51, .nonneg 52, .branchLe 46 (0), .branchLe 30 (0), .branchGe 31 (1)]

def plane458GenLeaf0002Mult : Fin 57 → Nat := ![1243, 696, 5008, 14597, 3259, 10784, 2927, 7061, 4019, 3292, 6819, 21089, 10660, 1973, 6565, 9603, 11867, 292, 6763, 241, 3054, 524, 3074, 2843, 6559, 10655, 18506, 2169, 7845, 10800, 7060, 1379, 7052, 1817, 201, 6639, 7413, 4992, 5440, 4357, 1299, 673, 884, 3077, 28109, 1447, 7991, 2580, 782, 1930, 4924, 18302, 2268, 8083, 25035, 28109, 103052]

theorem plane458GenLeaf0002 (x : Fin 56 → Int)
    (hroot : plane458GenOccSys.RootHolds x)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane458GenLeaf0002Refs i).resolveCoeff plane458GenOccSys j)
    (fun i => (plane458GenLeaf0002Refs i).resolveRhs plane458GenOccSys) plane458GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane458GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 16
  · exact hroot.hOcc 21
  · exact hroot.hOcc 27
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 39
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 49
  · exact hroot.hOcc 52
  · exact hroot.hOcc 54
  · exact hroot.hOcc 60
  · exact hroot.hOcc 67
  · exact hroot.hOcc 70
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 78
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 95
  · exact hroot.hOcc 98
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 123
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 149
  · exact hroot.hOcc 151
  · exact hroot.hOcc 161
  · exact hroot.hOcc 167
  · exact hroot.hOcc 168
  · exact hroot.hOcc 176
  · exact hroot.hOcc 189
  · exact hroot.hOcc 195
  · exact hroot.hOcc 197
  · exact hroot.hOcc 202
  · change (∑ j, (-1 : Int) * x j) ≤ -plane458GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (13 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (25 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (29 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (32 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (37 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (43 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (51 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (52 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (46 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (30 : Fin 56) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (31 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31

end QiushiMatmul
