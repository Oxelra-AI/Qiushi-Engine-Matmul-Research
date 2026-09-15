import QiushiPlane425GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane425GenLeaf0005Refs : Fin 59 → RowRef 202 58 := ![.occ 6, .occ 13, .occ 15, .occ 29, .occ 30, .occ 33, .occ 43, .occ 48, .occ 51, .occ 60, .occ 61, .occ 62, .occ 72, .occ 76, .occ 85, .occ 88, .occ 93, .occ 94, .occ 100, .occ 107, .occ 117, .occ 119, .occ 124, .occ 125, .occ 127, .occ 138, .occ 139, .occ 148, .occ 151, .occ 153, .occ 158, .occ 170, .occ 176, .occ 178, .occ 179, .occ 183, .occ 185, .occ 186, .occ 190, .occ 191, .occ 199, .sumGe, .nonneg 2, .nonneg 13, .nonneg 14, .nonneg 15, .nonneg 22, .nonneg 23, .nonneg 38, .nonneg 41, .nonneg 45, .nonneg 48, .nonneg 51, .nonneg 55, .nonneg 56, .branchGe 17 (1), .branchLe 9 (0), .branchLe 43 (0), .branchGe 20 (1)]

def plane425GenLeaf0005Mult : Fin 59 → Nat := ![2670, 7160, 9328, 2508, 6786, 7386, 12128, 4240, 2154, 1978, 578, 5720, 7034, 5152, 814, 11452, 4486, 5624, 1978, 3042, 570, 618, 3008, 3939, 2208, 261, 3070, 607, 1388, 2793, 3163, 4904, 727, 1325, 3817, 4006, 4834, 621, 1282, 4305, 3004, 19150, 1054, 8222, 3496, 6844, 2438, 3262, 10772, 5978, 2862, 5290, 9752, 9864, 5128, 14656, 5528, 16146, 75534]

theorem plane425GenLeaf0005 (x : Fin 58 → Int)
    (hroot : plane425GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane425GenLeaf0005Refs i).resolveCoeff plane425GenOccSys j)
    (fun i => (plane425GenLeaf0005Refs i).resolveRhs plane425GenOccSys) plane425GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane425GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 13
  · exact hroot.hOcc 15
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 33
  · exact hroot.hOcc 43
  · exact hroot.hOcc 48
  · exact hroot.hOcc 51
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 72
  · exact hroot.hOcc 76
  · exact hroot.hOcc 85
  · exact hroot.hOcc 88
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 100
  · exact hroot.hOcc 107
  · exact hroot.hOcc 117
  · exact hroot.hOcc 119
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 148
  · exact hroot.hOcc 151
  · exact hroot.hOcc 153
  · exact hroot.hOcc 158
  · exact hroot.hOcc 170
  · exact hroot.hOcc 176
  · exact hroot.hOcc 178
  · exact hroot.hOcc 179
  · exact hroot.hOcc 183
  · exact hroot.hOcc 185
  · exact hroot.hOcc 186
  · exact hroot.hOcc 190
  · exact hroot.hOcc 191
  · exact hroot.hOcc 199
  · change (∑ j, (-1 : Int) * x j) ≤ -plane425GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (13 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (22 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (38 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (41 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (45 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (48 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (51 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (55 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (56 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (9 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (20 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
