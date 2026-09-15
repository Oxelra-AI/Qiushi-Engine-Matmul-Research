import QiushiPlane468GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane468GenLeaf0006Refs : Fin 63 → RowRef 253 62 := ![.occ 6, .occ 8, .occ 21, .occ 28, .occ 34, .occ 51, .occ 52, .occ 77, .occ 83, .occ 84, .occ 92, .occ 99, .occ 105, .occ 107, .occ 111, .occ 116, .occ 120, .occ 121, .occ 124, .occ 126, .occ 127, .occ 130, .occ 139, .occ 152, .occ 155, .occ 158, .occ 160, .occ 183, .occ 184, .occ 189, .occ 199, .occ 211, .occ 226, .occ 229, .occ 236, .occ 237, .occ 238, .occ 239, .occ 240, .occ 242, .occ 247, .occ 248, .occ 249, .occ 250, .sumGe, .nonneg 8, .nonneg 10, .nonneg 20, .nonneg 30, .nonneg 32, .nonneg 34, .nonneg 37, .nonneg 39, .nonneg 41, .nonneg 50, .nonneg 53, .nonneg 56, .nonneg 60, .branchLe 28 (0), .branchGe 51 (1), .branchGe 2 (1), .branchLe 1 (0), .branchGe 49 (1)]

def plane468GenLeaf0006Mult : Fin 63 → Nat := ![79806, 234738, 124894, 395098, 108150, 264230, 89782, 128048, 553546, 166912, 769618, 195134, 98960, 617660, 874110, 712680, 15386, 352290, 258344, 178822, 77130, 708234, 14910, 17238, 68198, 210462, 123940, 302616, 427956, 184194, 282186, 6918, 444020, 133020, 124178, 1945, 90173, 90615, 235053, 74960, 529128, 393951, 53611, 282342, 1842140, 98114, 944782, 564928, 272664, 158590, 964924, 323848, 469782, 644482, 752726, 175752, 1144726, 1068810, 935890, 1968914, 1560236, 1842140, 3828128]

theorem plane468GenLeaf0006 (x : Fin 62 → Int)
    (hroot : plane468GenOccSys.RootHolds x)
    (hLB_51 : (1 : Int) ≤ x 51)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_49 : (1 : Int) ≤ x 49)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane468GenLeaf0006Refs i).resolveCoeff plane468GenOccSys j)
    (fun i => (plane468GenLeaf0006Refs i).resolveRhs plane468GenOccSys) plane468GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane468GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 6
  · exact hroot.hOcc 8
  · exact hroot.hOcc 21
  · exact hroot.hOcc 28
  · exact hroot.hOcc 34
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 77
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 92
  · exact hroot.hOcc 99
  · exact hroot.hOcc 105
  · exact hroot.hOcc 107
  · exact hroot.hOcc 111
  · exact hroot.hOcc 116
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 139
  · exact hroot.hOcc 152
  · exact hroot.hOcc 155
  · exact hroot.hOcc 158
  · exact hroot.hOcc 160
  · exact hroot.hOcc 183
  · exact hroot.hOcc 184
  · exact hroot.hOcc 189
  · exact hroot.hOcc 199
  · exact hroot.hOcc 211
  · exact hroot.hOcc 226
  · exact hroot.hOcc 229
  · exact hroot.hOcc 236
  · exact hroot.hOcc 237
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 240
  · exact hroot.hOcc 242
  · exact hroot.hOcc 247
  · exact hroot.hOcc 248
  · exact hroot.hOcc 249
  · exact hroot.hOcc 250
  · change (∑ j, (-1 : Int) * x j) ≤ -plane468GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (34 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (37 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (41 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (50 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (56 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (60 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (28 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_51
  · change (∑ k, (if k = (2 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (1 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (49 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_49

end QiushiMatmul
