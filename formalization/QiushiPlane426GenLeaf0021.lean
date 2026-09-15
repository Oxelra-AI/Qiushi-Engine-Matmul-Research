import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0021Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 26, .occ 34, .occ 64, .occ 68, .occ 78, .occ 88, .occ 102, .occ 109, .occ 113, .occ 117, .occ 120, .occ 121, .occ 122, .occ 123, .occ 124, .occ 131, .occ 136, .occ 157, .occ 160, .occ 185, .occ 186, .occ 201, .occ 205, .occ 231, .occ 260, .occ 261, .occ 272, .occ 274, .occ 279, .occ 280, .occ 281, .occ 299, .occ 303, .occ 309, .occ 325, .occ 331, .occ 335, .sumGe, .nonneg 5, .nonneg 7, .nonneg 8, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 21, .nonneg 25, .nonneg 28, .nonneg 36, .nonneg 40, .nonneg 47, .nonneg 50, .branchLe 43 (0), .branchGe 14 (1), .branchLe 42 (0), .branchLe 18 (0), .branchLe 56 (0), .branchLe 11 (0), .branchGe 6 (1)]

def plane426GenLeaf0021Mult : Fin 59 → Nat := ![167742, 70880, 34297, 108072, 694305, 296072, 349898, 170323, 28380, 248915, 176925, 58627, 242923, 57352, 97182, 43090, 140441, 105742, 66835, 285083, 64893, 93678, 51486, 189320, 66291, 127721, 220246, 23042, 32468, 111444, 48855, 128963, 115679, 41913, 36859, 189975, 96173, 48847, 743152, 283824, 93678, 37304, 398688, 447115, 128037, 384000, 160124, 134473, 146566, 18997, 70880, 308497, 535104, 880663, 66824, 410931, 205210, 685800, 2260482]

theorem plane426GenLeaf0021 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_56 : x 56 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0021Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0021Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0021Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0021Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 26
  · exact hroot.hOcc 34
  · exact hroot.hOcc 64
  · exact hroot.hOcc 68
  · exact hroot.hOcc 78
  · exact hroot.hOcc 88
  · exact hroot.hOcc 102
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 117
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 131
  · exact hroot.hOcc 136
  · exact hroot.hOcc 157
  · exact hroot.hOcc 160
  · exact hroot.hOcc 185
  · exact hroot.hOcc 186
  · exact hroot.hOcc 201
  · exact hroot.hOcc 205
  · exact hroot.hOcc 231
  · exact hroot.hOcc 260
  · exact hroot.hOcc 261
  · exact hroot.hOcc 272
  · exact hroot.hOcc 274
  · exact hroot.hOcc 279
  · exact hroot.hOcc 280
  · exact hroot.hOcc 281
  · exact hroot.hOcc 299
  · exact hroot.hOcc 303
  · exact hroot.hOcc 309
  · exact hroot.hOcc 325
  · exact hroot.hOcc 331
  · exact hroot.hOcc 335
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (7 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (21 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (40 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (42 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (18 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (56 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_56
  · change (∑ k, (if k = (11 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (6 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
