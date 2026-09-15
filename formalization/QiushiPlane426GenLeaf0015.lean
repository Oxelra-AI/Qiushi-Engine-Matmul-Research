import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0015Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 21, .occ 52, .occ 61, .occ 65, .occ 71, .occ 79, .occ 86, .occ 88, .occ 91, .occ 103, .occ 104, .occ 114, .occ 116, .occ 123, .occ 124, .occ 144, .occ 145, .occ 160, .occ 186, .occ 197, .occ 205, .occ 208, .occ 210, .occ 225, .occ 228, .occ 235, .occ 237, .occ 242, .occ 278, .occ 279, .occ 284, .occ 290, .occ 312, .occ 313, .occ 314, .occ 315, .occ 322, .occ 330, .occ 333, .occ 334, .occ 335, .sumGe, .nonneg 5, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 25, .nonneg 26, .nonneg 28, .nonneg 36, .nonneg 50, .nonneg 55, .branchLe 43 (0), .branchLe 14 (0), .branchGe 1 (1), .branchGe 35 (1), .branchLe 13 (0), .branchLe 20 (0)]

def plane426GenLeaf0015Mult : Fin 59 → Nat := ![4341, 609, 220, 3613, 1013, 2099, 1566, 81, 1721, 154, 77, 2524, 2011, 2441, 2144, 2441, 1100, 609, 1780, 1516, 701, 1013, 62, 154, 1503, 395, 250, 738, 1016, 202, 476, 17, 363, 1079, 236, 202, 48, 644, 69, 1166, 1010, 621, 6302, 4246, 3858, 11451, 6771, 3797, 85, 2218, 250, 3763, 455, 5194, 6156, 5699, 10231, 1678, 6019]

theorem plane426GenLeaf0015 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0015Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0015Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0015Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0015Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 21
  · exact hroot.hOcc 52
  · exact hroot.hOcc 61
  · exact hroot.hOcc 65
  · exact hroot.hOcc 71
  · exact hroot.hOcc 79
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 91
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 144
  · exact hroot.hOcc 145
  · exact hroot.hOcc 160
  · exact hroot.hOcc 186
  · exact hroot.hOcc 197
  · exact hroot.hOcc 205
  · exact hroot.hOcc 208
  · exact hroot.hOcc 210
  · exact hroot.hOcc 225
  · exact hroot.hOcc 228
  · exact hroot.hOcc 235
  · exact hroot.hOcc 237
  · exact hroot.hOcc 242
  · exact hroot.hOcc 278
  · exact hroot.hOcc 279
  · exact hroot.hOcc 284
  · exact hroot.hOcc 290
  · exact hroot.hOcc 312
  · exact hroot.hOcc 313
  · exact hroot.hOcc 314
  · exact hroot.hOcc 315
  · exact hroot.hOcc 322
  · exact hroot.hOcc 330
  · exact hroot.hOcc 333
  · exact hroot.hOcc 334
  · exact hroot.hOcc 335
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (55 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (35 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (13 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (20 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20

end QiushiMatmul
