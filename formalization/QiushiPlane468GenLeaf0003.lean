import QiushiPlane468GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane468GenLeaf0003Refs : Fin 63 → RowRef 253 62 := ![.occ 2, .occ 5, .occ 7, .occ 8, .occ 10, .occ 18, .occ 25, .occ 27, .occ 63, .occ 65, .occ 77, .occ 78, .occ 79, .occ 84, .occ 93, .occ 99, .occ 103, .occ 107, .occ 116, .occ 124, .occ 125, .occ 126, .occ 135, .occ 137, .occ 139, .occ 145, .occ 153, .occ 162, .occ 163, .occ 167, .occ 169, .occ 171, .occ 185, .occ 194, .occ 195, .occ 224, .occ 231, .occ 232, .occ 234, .occ 236, .occ 237, .occ 239, .occ 242, .occ 243, .occ 245, .sumGe, .nonneg 10, .nonneg 30, .nonneg 31, .nonneg 32, .nonneg 39, .nonneg 41, .nonneg 42, .nonneg 44, .nonneg 50, .nonneg 59, .nonneg 60, .branchLe 28 (0), .branchGe 51 (1), .branchLe 15 (0), .branchLe 2 (0), .branchLe 33 (0), .branchGe 4 (1)]

def plane468GenLeaf0003Mult : Fin 63 → Nat := ![123938, 476589, 75241, 18647, 46164, 73004, 68021, 2854, 131400, 269786, 252592, 76780, 77408, 115198, 84140, 267709, 23069, 133520, 179767, 420440, 143874, 66744, 254580, 125486, 106180, 37079, 38869, 32985, 80241, 84621, 115635, 49567, 89015, 35598, 48864, 26663, 89034, 63276, 17623, 193570, 97850, 180772, 31922, 41237, 23029, 686502, 177282, 243236, 13969, 175226, 581079, 115501, 60430, 53272, 97944, 379014, 195794, 464493, 408058, 490626, 686502, 507038, 1779926]

theorem plane468GenLeaf0003 (x : Fin 62 → Int)
    (hroot : plane468GenOccSys.RootHolds x)
    (hLB_51 : (1 : Int) ≤ x 51)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane468GenLeaf0003Refs i).resolveCoeff plane468GenOccSys j)
    (fun i => (plane468GenLeaf0003Refs i).resolveRhs plane468GenOccSys) plane468GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane468GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 5
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 10
  · exact hroot.hOcc 18
  · exact hroot.hOcc 25
  · exact hroot.hOcc 27
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 84
  · exact hroot.hOcc 93
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 107
  · exact hroot.hOcc 116
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 145
  · exact hroot.hOcc 153
  · exact hroot.hOcc 162
  · exact hroot.hOcc 163
  · exact hroot.hOcc 167
  · exact hroot.hOcc 169
  · exact hroot.hOcc 171
  · exact hroot.hOcc 185
  · exact hroot.hOcc 194
  · exact hroot.hOcc 195
  · exact hroot.hOcc 224
  · exact hroot.hOcc 231
  · exact hroot.hOcc 232
  · exact hroot.hOcc 234
  · exact hroot.hOcc 236
  · exact hroot.hOcc 237
  · exact hroot.hOcc 239
  · exact hroot.hOcc 242
  · exact hroot.hOcc 243
  · exact hroot.hOcc 245
  · change (∑ j, (-1 : Int) * x j) ≤ -plane468GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (31 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (41 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (42 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (50 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (60 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (28 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_51
  · change (∑ k, (if k = (15 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (33 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (4 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
