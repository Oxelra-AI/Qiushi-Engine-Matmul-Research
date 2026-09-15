import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0017Refs : Fin 63 → RowRef 294 62 := ![.occ 22, .occ 28, .occ 30, .occ 32, .occ 33, .occ 39, .occ 41, .occ 47, .occ 49, .occ 50, .occ 62, .occ 67, .occ 73, .occ 76, .occ 78, .occ 80, .occ 81, .occ 84, .occ 85, .occ 88, .occ 89, .occ 91, .occ 97, .occ 102, .occ 105, .occ 109, .occ 136, .occ 152, .occ 154, .occ 163, .occ 165, .occ 168, .occ 178, .occ 190, .occ 205, .occ 209, .occ 234, .occ 244, .occ 253, .occ 260, .occ 276, .occ 278, .occ 283, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 23, .nonneg 38, .nonneg 41, .nonneg 47, .nonneg 48, .nonneg 51, .nonneg 57, .nonneg 59, .nonneg 61, .branchGe 5 (1), .branchGe 24 (1), .branchGe 27 (1), .branchLe 9 (0), .branchGe 16 (1), .branchLe 1 (0), .branchGe 34 (2)]

def plane462GenLeaf0017Mult : Fin 63 → Nat := ![309, 19, 982, 576, 320, 812, 4, 788, 1269, 246, 1142, 1084, 335, 768, 1229, 894, 405, 1289, 891, 406, 687, 476, 465, 858, 896, 878, 711, 119, 455, 282, 130, 154, 280, 291, 201, 282, 280, 1252, 9, 239, 125, 98, 353, 2633, 2858, 5816, 2552, 238, 1576, 1396, 972, 826, 2292, 1174, 494, 1174, 750, 3585, 750, 2503, 3223, 2197, 5256]

theorem plane462GenLeaf0017 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_34 : (2 : Int) ≤ x 34)
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0017Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0017Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0017Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0017Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 22
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 39
  · exact hroot.hOcc 41
  · exact hroot.hOcc 47
  · exact hroot.hOcc 49
  · exact hroot.hOcc 50
  · exact hroot.hOcc 62
  · exact hroot.hOcc 67
  · exact hroot.hOcc 73
  · exact hroot.hOcc 76
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 97
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 109
  · exact hroot.hOcc 136
  · exact hroot.hOcc 152
  · exact hroot.hOcc 154
  · exact hroot.hOcc 163
  · exact hroot.hOcc 165
  · exact hroot.hOcc 168
  · exact hroot.hOcc 178
  · exact hroot.hOcc 190
  · exact hroot.hOcc 205
  · exact hroot.hOcc 209
  · exact hroot.hOcc 234
  · exact hroot.hOcc 244
  · exact hroot.hOcc 253
  · exact hroot.hOcc 260
  · exact hroot.hOcc 276
  · exact hroot.hOcc 278
  · exact hroot.hOcc 283
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (23 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (38 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (41 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (47 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (48 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (61 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (5 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (24 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (27 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (9 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (16 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (1 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (34 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34

end QiushiMatmul
