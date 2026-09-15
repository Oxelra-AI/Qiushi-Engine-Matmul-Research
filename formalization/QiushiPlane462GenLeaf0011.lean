import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0011Refs : Fin 63 → RowRef 294 62 := ![.occ 14, .occ 26, .occ 44, .occ 47, .occ 49, .occ 57, .occ 60, .occ 64, .occ 67, .occ 68, .occ 71, .occ 72, .occ 73, .occ 76, .occ 79, .occ 81, .occ 84, .occ 86, .occ 89, .occ 91, .occ 92, .occ 94, .occ 96, .occ 99, .occ 102, .occ 103, .occ 110, .occ 131, .occ 146, .occ 148, .occ 166, .occ 173, .occ 181, .occ 190, .occ 246, .occ 268, .occ 274, .occ 275, .occ 276, .occ 282, .occ 285, .occ 287, .occ 288, .occ 290, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 11, .nonneg 17, .nonneg 25, .nonneg 29, .nonneg 40, .nonneg 41, .nonneg 47, .nonneg 51, .nonneg 53, .nonneg 54, .nonneg 61, .branchGe 3 (1), .branchGe 5 (1), .branchLe 24 (0), .branchLe 45 (0)]

def plane462GenLeaf0011Mult : Fin 63 → Nat := ![325968, 159306, 614466, 169152, 33456, 723312, 410188, 343488, 1263284, 249324, 897248, 285641, 597514, 308482, 24668, 291325, 514506, 397949, 1247336, 641343, 9055, 429536, 1203018, 635099, 331748, 570087, 762545, 37966, 37966, 37084, 569824, 114052, 396838, 20968, 42206, 755587, 1226795, 58369, 515367, 704856, 581376, 981389, 859770, 303139, 4478340, 2650760, 504116, 2665128, 623376, 529592, 474164, 2344392, 937226, 900038, 1784854, 4697788, 1002098, 1759058, 616570, 3949548, 970388, 4478340, 4364288]

theorem plane462GenLeaf0011 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_45 : x 45 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0011Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0011Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0011Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0011Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 26
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 49
  · exact hroot.hOcc 57
  · exact hroot.hOcc 60
  · exact hroot.hOcc 64
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 71
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 76
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 94
  · exact hroot.hOcc 96
  · exact hroot.hOcc 99
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 110
  · exact hroot.hOcc 131
  · exact hroot.hOcc 146
  · exact hroot.hOcc 148
  · exact hroot.hOcc 166
  · exact hroot.hOcc 173
  · exact hroot.hOcc 181
  · exact hroot.hOcc 190
  · exact hroot.hOcc 246
  · exact hroot.hOcc 268
  · exact hroot.hOcc 274
  · exact hroot.hOcc 275
  · exact hroot.hOcc 276
  · exact hroot.hOcc 282
  · exact hroot.hOcc 285
  · exact hroot.hOcc 287
  · exact hroot.hOcc 288
  · exact hroot.hOcc 290
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (11 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (17 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (25 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (29 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (41 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (47 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (54 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (61 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (5 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (24 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (45 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45

end QiushiMatmul
