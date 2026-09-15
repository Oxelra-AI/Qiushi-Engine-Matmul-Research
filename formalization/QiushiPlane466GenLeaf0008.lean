import QiushiPlane466GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane466GenLeaf0008Refs : Fin 51 → RowRef 210 50 := ![.occ 16, .occ 17, .occ 26, .occ 28, .occ 32, .occ 36, .occ 40, .occ 42, .occ 47, .occ 52, .occ 65, .occ 69, .occ 70, .occ 83, .occ 93, .occ 100, .occ 101, .occ 103, .occ 109, .occ 117, .occ 119, .occ 120, .occ 123, .occ 129, .occ 131, .occ 143, .occ 145, .occ 146, .occ 154, .occ 159, .occ 160, .occ 161, .occ 172, .occ 173, .occ 176, .occ 188, .occ 193, .occ 199, .occ 203, .occ 205, .sumGe, .nonneg 0, .nonneg 13, .nonneg 18, .nonneg 31, .nonneg 32, .nonneg 35, .nonneg 38, .nonneg 49, .branchGe 24 (1), .branchLe 28 (0)]

def plane466GenLeaf0008Mult : Fin 51 → Nat := ![9787, 9799, 872, 15523, 10489, 11653, 17828, 3328, 6457, 11109, 4749, 14136, 9727, 12196, 1737, 7337, 3440, 13515, 5119, 5530, 2884, 17840, 478, 2804, 491, 331, 1229, 11846, 189, 6816, 1011, 2476, 3790, 7553, 6348, 4846, 3834, 462, 4358, 681, 26810, 12252, 4819, 3802, 7584, 17308, 3675, 3239, 3753, 150740, 26348]

theorem plane466GenLeaf0008 (x : Fin 50 → Int)
    (hroot : plane466GenOccSys.RootHolds x)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane466GenLeaf0008Refs i).resolveCoeff plane466GenOccSys j)
    (fun i => (plane466GenLeaf0008Refs i).resolveRhs plane466GenOccSys) plane466GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane466GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 16
  · exact hroot.hOcc 17
  · exact hroot.hOcc 26
  · exact hroot.hOcc 28
  · exact hroot.hOcc 32
  · exact hroot.hOcc 36
  · exact hroot.hOcc 40
  · exact hroot.hOcc 42
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 65
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 83
  · exact hroot.hOcc 93
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 103
  · exact hroot.hOcc 109
  · exact hroot.hOcc 117
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 143
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 154
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 161
  · exact hroot.hOcc 172
  · exact hroot.hOcc 173
  · exact hroot.hOcc 176
  · exact hroot.hOcc 188
  · exact hroot.hOcc 193
  · exact hroot.hOcc 199
  · exact hroot.hOcc 203
  · exact hroot.hOcc 205
  · change (∑ j, (-1 : Int) * x j) ≤ -plane466GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (13 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (18 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (31 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (35 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (38 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (49 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (24 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (28 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
