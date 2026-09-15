import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0036Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 20, .occ 31, .occ 35, .occ 71, .occ 86, .occ 88, .occ 99, .occ 102, .occ 103, .occ 104, .occ 109, .occ 112, .occ 116, .occ 121, .occ 135, .occ 137, .occ 138, .occ 149, .occ 155, .occ 175, .occ 184, .occ 188, .occ 204, .occ 207, .occ 234, .occ 235, .occ 241, .occ 251, .occ 267, .occ 268, .occ 280, .occ 285, .occ 295, .occ 299, .occ 316, .occ 323, .occ 325, .occ 327, .occ 334, .sumGe, .nonneg 9, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 22, .nonneg 23, .nonneg 24, .nonneg 26, .nonneg 27, .nonneg 33, .nonneg 36, .nonneg 39, .nonneg 50, .nonneg 52, .nonneg 56, .branchGe 43 (1), .branchGe 34 (1), .branchGe 49 (1)]

def plane426GenLeaf0036Mult : Fin 59 → Nat := ![8721, 50356, 2487, 59392, 12244, 27332, 6873, 49253, 2733, 1497, 6073, 44372, 50953, 33441, 14417, 56447, 27516, 132585, 4641, 15401, 51983, 41066, 52472, 30169, 10311, 19197, 37178, 6643, 12388, 64003, 20072, 9319, 46526, 30291, 4384, 31470, 11739, 17311, 4173, 4923, 144324, 40110, 128880, 403796, 24448, 44933, 11795, 104492, 52299, 8282, 50223, 22234, 64967, 40508, 439, 22996, 590208, 58123, 320739]

theorem plane426GenLeaf0036 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_49 : (1 : Int) ≤ x 49)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0036Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0036Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0036Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0036Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 20
  · exact hroot.hOcc 31
  · exact hroot.hOcc 35
  · exact hroot.hOcc 71
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 99
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 121
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 149
  · exact hroot.hOcc 155
  · exact hroot.hOcc 175
  · exact hroot.hOcc 184
  · exact hroot.hOcc 188
  · exact hroot.hOcc 204
  · exact hroot.hOcc 207
  · exact hroot.hOcc 234
  · exact hroot.hOcc 235
  · exact hroot.hOcc 241
  · exact hroot.hOcc 251
  · exact hroot.hOcc 267
  · exact hroot.hOcc 268
  · exact hroot.hOcc 280
  · exact hroot.hOcc 285
  · exact hroot.hOcc 295
  · exact hroot.hOcc 299
  · exact hroot.hOcc 316
  · exact hroot.hOcc 323
  · exact hroot.hOcc 325
  · exact hroot.hOcc 327
  · exact hroot.hOcc 334
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (22 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (27 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (39 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (56 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (43 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (34 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (49 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_49

end QiushiMatmul
