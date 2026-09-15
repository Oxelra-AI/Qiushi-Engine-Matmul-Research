import QiushiPlane468GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane468GenLeaf0007Refs : Fin 63 → RowRef 253 62 := ![.occ 2, .occ 21, .occ 26, .occ 50, .occ 52, .occ 53, .occ 64, .occ 66, .occ 82, .occ 83, .occ 91, .occ 93, .occ 95, .occ 100, .occ 105, .occ 107, .occ 109, .occ 110, .occ 114, .occ 115, .occ 116, .occ 124, .occ 130, .occ 135, .occ 139, .occ 158, .occ 162, .occ 177, .occ 178, .occ 181, .occ 183, .occ 184, .occ 187, .occ 195, .occ 224, .occ 226, .occ 230, .occ 231, .occ 236, .occ 239, .occ 245, .occ 246, .occ 247, .occ 249, .occ 250, .sumGe, .nonneg 7, .nonneg 8, .nonneg 10, .nonneg 20, .nonneg 31, .nonneg 32, .nonneg 34, .nonneg 37, .nonneg 54, .nonneg 59, .branchLe 28 (0), .branchGe 51 (1), .branchLe 15 (0), .branchGe 2 (1), .branchGe 1 (1), .branchLe 11 (0), .branchLe 40 (0)]

def plane468GenLeaf0007Mult : Fin 63 → Nat := ![12662494, 3870276, 2154390, 5736718, 7300472, 386538, 10341874, 20086366, 7275298, 13529724, 347114, 6601648, 2204160, 20187148, 4549044, 9634494, 2150438, 4405740, 212780, 2435746, 3899182, 5079426, 11237400, 6040960, 5236368, 4521452, 4136480, 1554109, 537800, 3129973, 6169742, 9771975, 1245245, 5305466, 5947234, 2896208, 6092860, 2279394, 1866795, 2986386, 7290388, 2203355, 996576, 3738991, 5105506, 35281421, 1604728, 14753556, 15193894, 23763102, 402908, 5413342, 11813614, 9477458, 17860314, 2976160, 21072278, 48048104, 14721562, 49014120, 49185036, 26975984, 22853004]

theorem plane468GenLeaf0007 (x : Fin 62 → Int)
    (hroot : plane468GenOccSys.RootHolds x)
    (hLB_51 : (1 : Int) ≤ x 51)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane468GenLeaf0007Refs i).resolveCoeff plane468GenOccSys j)
    (fun i => (plane468GenLeaf0007Refs i).resolveRhs plane468GenOccSys) plane468GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane468GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 21
  · exact hroot.hOcc 26
  · exact hroot.hOcc 50
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 91
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 100
  · exact hroot.hOcc 105
  · exact hroot.hOcc 107
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 124
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 158
  · exact hroot.hOcc 162
  · exact hroot.hOcc 177
  · exact hroot.hOcc 178
  · exact hroot.hOcc 181
  · exact hroot.hOcc 183
  · exact hroot.hOcc 184
  · exact hroot.hOcc 187
  · exact hroot.hOcc 195
  · exact hroot.hOcc 224
  · exact hroot.hOcc 226
  · exact hroot.hOcc 230
  · exact hroot.hOcc 231
  · exact hroot.hOcc 236
  · exact hroot.hOcc 239
  · exact hroot.hOcc 245
  · exact hroot.hOcc 246
  · exact hroot.hOcc 247
  · exact hroot.hOcc 249
  · exact hroot.hOcc 250
  · change (∑ j, (-1 : Int) * x j) ≤ -plane468GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (31 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (37 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (54 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (28 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_51
  · change (∑ k, (if k = (15 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (1 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (11 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (40 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40

end QiushiMatmul
