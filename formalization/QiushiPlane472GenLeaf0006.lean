import QiushiPlane472GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane472GenLeaf0006Refs : Fin 63 → RowRef 242 62 := ![.occ 1, .occ 6, .occ 7, .occ 18, .occ 30, .occ 33, .occ 36, .occ 37, .occ 44, .occ 57, .occ 59, .occ 60, .occ 64, .occ 66, .occ 71, .occ 75, .occ 80, .occ 87, .occ 88, .occ 90, .occ 94, .occ 99, .occ 115, .occ 130, .occ 138, .occ 147, .occ 154, .occ 168, .occ 174, .occ 175, .occ 176, .occ 177, .occ 182, .occ 195, .occ 202, .occ 217, .occ 224, .occ 225, .occ 226, .occ 227, .occ 228, .occ 234, .occ 235, .sumGe, .nonneg 3, .nonneg 10, .nonneg 15, .nonneg 30, .nonneg 32, .nonneg 36, .nonneg 39, .nonneg 40, .nonneg 45, .nonneg 50, .nonneg 53, .nonneg 55, .nonneg 57, .nonneg 58, .branchLe 60 (0), .branchLe 4 (0), .branchLe 33 (0), .branchGe 11 (1), .branchGe 28 (1)]

def plane472GenLeaf0006Mult : Fin 63 → Nat := ![23680, 28164, 7580, 2072, 452, 4312, 12320, 23364, 14760, 1256, 22180, 1784, 11452, 4576, 52920, 12228, 36648, 34684, 8808, 13608, 19284, 16632, 27364, 19536, 6218, 1728, 8714, 3516, 30510, 15136, 4810, 1404, 8562, 3958, 3296, 540, 2908, 5438, 7979, 21592, 3891, 4687, 11975, 77718, 12248, 25792, 15144, 6496, 7760, 17656, 18128, 2264, 20832, 48232, 25076, 17144, 14100, 15048, 70852, 57348, 55040, 38636, 243048]

theorem plane472GenLeaf0006 (x : Fin 62 → Int)
    (hroot : plane472GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane472GenLeaf0006Refs i).resolveCoeff plane472GenOccSys j)
    (fun i => (plane472GenLeaf0006Refs i).resolveRhs plane472GenOccSys) plane472GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane472GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 6
  · exact hroot.hOcc 7
  · exact hroot.hOcc 18
  · exact hroot.hOcc 30
  · exact hroot.hOcc 33
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 44
  · exact hroot.hOcc 57
  · exact hroot.hOcc 59
  · exact hroot.hOcc 60
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 71
  · exact hroot.hOcc 75
  · exact hroot.hOcc 80
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 90
  · exact hroot.hOcc 94
  · exact hroot.hOcc 99
  · exact hroot.hOcc 115
  · exact hroot.hOcc 130
  · exact hroot.hOcc 138
  · exact hroot.hOcc 147
  · exact hroot.hOcc 154
  · exact hroot.hOcc 168
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 177
  · exact hroot.hOcc 182
  · exact hroot.hOcc 195
  · exact hroot.hOcc 202
  · exact hroot.hOcc 217
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 226
  · exact hroot.hOcc 227
  · exact hroot.hOcc 228
  · exact hroot.hOcc 234
  · exact hroot.hOcc 235
  · change (∑ j, (-1 : Int) * x j) ≤ -plane472GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (36 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (45 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (50 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (55 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (58 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (60 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (4 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (33 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (11 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (28 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
