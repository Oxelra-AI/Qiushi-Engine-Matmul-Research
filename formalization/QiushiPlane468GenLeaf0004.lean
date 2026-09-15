import QiushiPlane468GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane468GenLeaf0004Refs : Fin 63 → RowRef 253 62 := ![.occ 8, .occ 17, .occ 21, .occ 24, .occ 28, .occ 42, .occ 45, .occ 51, .occ 60, .occ 70, .occ 75, .occ 76, .occ 79, .occ 80, .occ 87, .occ 93, .occ 95, .occ 96, .occ 100, .occ 103, .occ 116, .occ 124, .occ 128, .occ 130, .occ 131, .occ 134, .occ 135, .occ 138, .occ 139, .occ 141, .occ 145, .occ 156, .occ 167, .occ 170, .occ 173, .occ 174, .occ 185, .occ 195, .occ 196, .occ 209, .occ 224, .occ 236, .occ 237, .occ 238, .occ 239, .occ 242, .occ 243, .occ 245, .occ 250, .sumGe, .nonneg 10, .nonneg 18, .nonneg 20, .nonneg 30, .nonneg 31, .nonneg 34, .nonneg 37, .nonneg 59, .branchLe 28 (0), .branchGe 51 (1), .branchLe 15 (0), .branchLe 2 (0), .branchGe 33 (1)]

def plane468GenLeaf0004Mult : Fin 63 → Nat := ![4064229, 27629786, 7362020, 7938125, 3108903, 3693482, 26742083, 14667092, 2813600, 94444, 5964787, 31118834, 6041965, 9517398, 31338741, 23942575, 9110364, 671950, 21086878, 1825995, 21424075, 25665014, 8883758, 1578438, 456910, 3269056, 5231222, 10810532, 6851427, 1496163, 3753911, 2436895, 37992, 65885, 6773843, 10770087, 576924, 6779610, 2414554, 4877727, 12888323, 2993639, 5328251, 10074293, 6068668, 16881961, 2948525, 18066271, 2167253, 64855529, 5359883, 13508357, 29916332, 1069343, 247301, 24349142, 4574822, 33065777, 55772451, 80625831, 52613983, 62688276, 172471599]

theorem plane468GenLeaf0004 (x : Fin 62 → Int)
    (hroot : plane468GenOccSys.RootHolds x)
    (hLB_51 : (1 : Int) ≤ x 51)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane468GenLeaf0004Refs i).resolveCoeff plane468GenOccSys j)
    (fun i => (plane468GenLeaf0004Refs i).resolveRhs plane468GenOccSys) plane468GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane468GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 17
  · exact hroot.hOcc 21
  · exact hroot.hOcc 24
  · exact hroot.hOcc 28
  · exact hroot.hOcc 42
  · exact hroot.hOcc 45
  · exact hroot.hOcc 51
  · exact hroot.hOcc 60
  · exact hroot.hOcc 70
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 87
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 116
  · exact hroot.hOcc 124
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 145
  · exact hroot.hOcc 156
  · exact hroot.hOcc 167
  · exact hroot.hOcc 170
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 185
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 209
  · exact hroot.hOcc 224
  · exact hroot.hOcc 236
  · exact hroot.hOcc 237
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 242
  · exact hroot.hOcc 243
  · exact hroot.hOcc 245
  · exact hroot.hOcc 250
  · change (∑ j, (-1 : Int) * x j) ≤ -plane468GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (18 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (31 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (34 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (37 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (28 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_51
  · change (∑ k, (if k = (15 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (33 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
