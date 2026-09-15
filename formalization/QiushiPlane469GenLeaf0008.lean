import QiushiPlane469GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane469GenLeaf0008Refs : Fin 61 → RowRef 217 60 := ![.occ 10, .occ 13, .occ 22, .occ 24, .occ 36, .occ 41, .occ 44, .occ 57, .occ 58, .occ 63, .occ 64, .occ 65, .occ 66, .occ 67, .occ 68, .occ 69, .occ 79, .occ 80, .occ 84, .occ 87, .occ 93, .occ 94, .occ 97, .occ 100, .occ 103, .occ 111, .occ 135, .occ 139, .occ 140, .occ 142, .occ 145, .occ 146, .occ 149, .occ 151, .occ 158, .occ 161, .occ 162, .occ 168, .occ 171, .occ 173, .occ 177, .occ 179, .occ 190, .occ 192, .occ 202, .occ 208, .sumGe, .nonneg 3, .nonneg 10, .nonneg 17, .nonneg 19, .nonneg 25, .nonneg 32, .nonneg 44, .nonneg 51, .nonneg 52, .nonneg 53, .nonneg 54, .nonneg 55, .nonneg 57, .branchGe 34 (1)]

def plane469GenLeaf0008Mult : Fin 61 → Nat := ![161446, 3718336, 1874528, 776096, 5085835, 1121260, 1415274, 409538, 1413364, 213349, 386385, 2603707, 481102, 439147, 1847824, 695822, 2198143, 1394971, 990090, 2694317, 1396472, 2182448, 236246, 1320942, 1825801, 4762634, 1899090, 491286, 36142, 3672471, 223386, 1774988, 182120, 74361, 622318, 346772, 537657, 67220, 1279373, 1170842, 2248888, 49918, 157265, 1973910, 211932, 32986, 6893809, 1402124, 1946396, 2678646, 326781, 973416, 2420392, 511645, 232158, 252226, 113106, 957104, 509238, 261148, 38431029]

theorem plane469GenLeaf0008 (x : Fin 60 → Int)
    (hroot : plane469GenOccSys.RootHolds x)
    (hLB_34 : (1 : Int) ≤ x 34)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane469GenLeaf0008Refs i).resolveCoeff plane469GenOccSys j)
    (fun i => (plane469GenLeaf0008Refs i).resolveRhs plane469GenOccSys) plane469GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane469GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · exact hroot.hOcc 13
  · exact hroot.hOcc 22
  · exact hroot.hOcc 24
  · exact hroot.hOcc 36
  · exact hroot.hOcc 41
  · exact hroot.hOcc 44
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 84
  · exact hroot.hOcc 87
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 111
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 149
  · exact hroot.hOcc 151
  · exact hroot.hOcc 158
  · exact hroot.hOcc 161
  · exact hroot.hOcc 162
  · exact hroot.hOcc 168
  · exact hroot.hOcc 171
  · exact hroot.hOcc 173
  · exact hroot.hOcc 177
  · exact hroot.hOcc 179
  · exact hroot.hOcc 190
  · exact hroot.hOcc 192
  · exact hroot.hOcc 202
  · exact hroot.hOcc 208
  · change (∑ j, (-1 : Int) * x j) ≤ -plane469GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (10 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (17 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (25 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (32 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (44 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (51 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (52 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (53 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (54 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (55 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (57 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (34 : Fin 60) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34

end QiushiMatmul
