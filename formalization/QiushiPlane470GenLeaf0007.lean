import QiushiPlane470GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane470GenLeaf0007Refs : Fin 64 → RowRef 232 63 := ![.occ 1, .occ 3, .occ 5, .occ 9, .occ 10, .occ 16, .occ 17, .occ 18, .occ 23, .occ 41, .occ 48, .occ 50, .occ 53, .occ 66, .occ 72, .occ 76, .occ 77, .occ 80, .occ 84, .occ 96, .occ 102, .occ 103, .occ 106, .occ 110, .occ 112, .occ 114, .occ 126, .occ 133, .occ 135, .occ 143, .occ 147, .occ 163, .occ 164, .occ 166, .occ 177, .occ 188, .occ 189, .occ 199, .occ 201, .occ 202, .occ 206, .occ 211, .occ 216, .occ 221, .occ 222, .occ 229, .sumGe, .nonneg 8, .nonneg 10, .nonneg 11, .nonneg 16, .nonneg 19, .nonneg 26, .nonneg 30, .nonneg 38, .nonneg 42, .nonneg 45, .nonneg 50, .nonneg 51, .nonneg 55, .nonneg 57, .nonneg 59, .branchGe 12 (1), .branchLe 18 (0)]

def plane470GenLeaf0007Mult : Fin 64 → Nat := ![154971, 72195, 160874, 70298, 19410, 122272, 82796, 159130, 11310, 117556, 105574, 109552, 35221, 140455, 67212, 76174, 49560, 38666, 101908, 574, 23064, 122696, 93960, 51122, 93926, 6734, 58268, 3512, 19773, 3715, 12392, 31833, 29077, 12055, 9259, 23703, 14608, 61950, 3894, 19838, 11069, 5676, 29097, 4383, 4474, 26217, 195769, 2176, 23552, 13924, 277776, 175668, 82402, 17906, 29284, 76758, 47406, 86464, 72910, 67402, 12396, 5276, 1394546, 166672]

theorem plane470GenLeaf0007 (x : Fin 63 → Int)
    (hroot : plane470GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hUB_18 : x 18 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane470GenLeaf0007Refs i).resolveCoeff plane470GenOccSys j)
    (fun i => (plane470GenLeaf0007Refs i).resolveRhs plane470GenOccSys) plane470GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane470GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 3
  · exact hroot.hOcc 5
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 18
  · exact hroot.hOcc 23
  · exact hroot.hOcc 41
  · exact hroot.hOcc 48
  · exact hroot.hOcc 50
  · exact hroot.hOcc 53
  · exact hroot.hOcc 66
  · exact hroot.hOcc 72
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 80
  · exact hroot.hOcc 84
  · exact hroot.hOcc 96
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 110
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 126
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 143
  · exact hroot.hOcc 147
  · exact hroot.hOcc 163
  · exact hroot.hOcc 164
  · exact hroot.hOcc 166
  · exact hroot.hOcc 177
  · exact hroot.hOcc 188
  · exact hroot.hOcc 189
  · exact hroot.hOcc 199
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 206
  · exact hroot.hOcc 211
  · exact hroot.hOcc 216
  · exact hroot.hOcc 221
  · exact hroot.hOcc 222
  · exact hroot.hOcc 229
  · change (∑ j, (-1 : Int) * x j) ≤ -plane470GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (16 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (19 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (30 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (45 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (50 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (57 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (12 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (18 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18

end QiushiMatmul
