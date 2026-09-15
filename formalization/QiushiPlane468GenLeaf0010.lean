import QiushiPlane468GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane468GenLeaf0010Refs : Fin 63 → RowRef 253 62 := ![.occ 1, .occ 2, .occ 3, .occ 8, .occ 19, .occ 40, .occ 49, .occ 58, .occ 62, .occ 66, .occ 69, .occ 70, .occ 72, .occ 87, .occ 88, .occ 102, .occ 103, .occ 105, .occ 107, .occ 116, .occ 121, .occ 124, .occ 129, .occ 132, .occ 133, .occ 135, .occ 136, .occ 140, .occ 162, .occ 166, .occ 169, .occ 170, .occ 176, .occ 179, .occ 186, .occ 190, .occ 201, .occ 202, .occ 212, .occ 215, .occ 217, .occ 218, .occ 238, .occ 245, .occ 247, .sumGe, .nonneg 8, .nonneg 20, .nonneg 30, .nonneg 31, .nonneg 34, .nonneg 37, .nonneg 39, .nonneg 44, .nonneg 45, .nonneg 53, .nonneg 54, .nonneg 56, .nonneg 59, .nonneg 60, .branchLe 28 (0), .branchGe 51 (1), .branchGe 15 (1)]

def plane468GenLeaf0010Mult : Fin 63 → Nat := ![143821, 2034, 20534, 3201, 4898, 46675, 24941, 78750, 110639, 42154, 81176, 20491, 71531, 17927, 70425, 22688, 22361, 84750, 41693, 40522, 102841, 6960, 41760, 19759, 9778, 7910, 12569, 29678, 14861, 21416, 21473, 9409, 20662, 40434, 31007, 25713, 77669, 4385, 5390, 3577, 18645, 33070, 43770, 11885, 23827, 187591, 15009, 23328, 80271, 18845, 42481, 73103, 8086, 17671, 37151, 28934, 31514, 29466, 48018, 41311, 79851, 78848, 1039899]

theorem plane468GenLeaf0010 (x : Fin 62 → Int)
    (hroot : plane468GenOccSys.RootHolds x)
    (hLB_51 : (1 : Int) ≤ x 51)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane468GenLeaf0010Refs i).resolveCoeff plane468GenOccSys j)
    (fun i => (plane468GenLeaf0010Refs i).resolveRhs plane468GenOccSys) plane468GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane468GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 2
  · exact hroot.hOcc 3
  · exact hroot.hOcc 8
  · exact hroot.hOcc 19
  · exact hroot.hOcc 40
  · exact hroot.hOcc 49
  · exact hroot.hOcc 58
  · exact hroot.hOcc 62
  · exact hroot.hOcc 66
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 72
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 107
  · exact hroot.hOcc 116
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 140
  · exact hroot.hOcc 162
  · exact hroot.hOcc 166
  · exact hroot.hOcc 169
  · exact hroot.hOcc 170
  · exact hroot.hOcc 176
  · exact hroot.hOcc 179
  · exact hroot.hOcc 186
  · exact hroot.hOcc 190
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 212
  · exact hroot.hOcc 215
  · exact hroot.hOcc 217
  · exact hroot.hOcc 218
  · exact hroot.hOcc 238
  · exact hroot.hOcc 245
  · exact hroot.hOcc 247
  · change (∑ j, (-1 : Int) * x j) ≤ -plane468GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (31 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (34 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (37 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (44 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (45 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (54 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (56 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (60 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (28 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_51
  · change (∑ k, (if k = (15 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15

end QiushiMatmul
