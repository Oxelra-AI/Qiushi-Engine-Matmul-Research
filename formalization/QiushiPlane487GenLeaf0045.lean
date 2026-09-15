import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0045Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 85, .occ 118, .occ 119, .occ 139, .occ 185, .occ 195, .occ 216, .occ 217, .occ 225, .occ 237, .occ 239, .occ 248, .occ 253, .occ 275, .occ 288, .occ 294, .occ 304, .occ 313, .occ 315, .occ 321, .occ 322, .occ 329, .occ 335, .occ 337, .occ 339, .occ 377, .occ 379, .occ 386, .occ 387, .occ 390, .occ 479, .occ 503, .occ 523, .occ 539, .occ 623, .occ 651, .occ 653, .occ 664, .occ 666, .sumGe, .nonneg 8, .nonneg 28, .nonneg 44, .branchLe 39 (0), .branchGe 23 (1), .branchGe 2 (1), .branchLe 6 (0), .branchGe 12 (1)]

def plane487GenLeaf0045Mult : Fin 49 → Nat := ![15848, 2298, 15006, 4463, 21882, 16685, 6973, 2310, 6534, 2134, 19946, 35918, 17257, 5678, 225, 2605, 3172, 6178, 17316, 21732, 19961, 11419, 2556, 28220, 1214, 3363, 5916, 17080, 8695, 2619, 7860, 484, 5709, 7019, 389, 5369, 6488, 1745, 7019, 6908, 49650, 8886, 28305, 5694, 40402, 172873, 33154, 46478, 114132]

theorem plane487GenLeaf0045 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0045Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0045Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0045Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0045Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 139
  · exact hroot.hOcc 185
  · exact hroot.hOcc 195
  · exact hroot.hOcc 216
  · exact hroot.hOcc 217
  · exact hroot.hOcc 225
  · exact hroot.hOcc 237
  · exact hroot.hOcc 239
  · exact hroot.hOcc 248
  · exact hroot.hOcc 253
  · exact hroot.hOcc 275
  · exact hroot.hOcc 288
  · exact hroot.hOcc 294
  · exact hroot.hOcc 304
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 321
  · exact hroot.hOcc 322
  · exact hroot.hOcc 329
  · exact hroot.hOcc 335
  · exact hroot.hOcc 337
  · exact hroot.hOcc 339
  · exact hroot.hOcc 377
  · exact hroot.hOcc 379
  · exact hroot.hOcc 386
  · exact hroot.hOcc 387
  · exact hroot.hOcc 390
  · exact hroot.hOcc 479
  · exact hroot.hOcc 503
  · exact hroot.hOcc 523
  · exact hroot.hOcc 539
  · exact hroot.hOcc 623
  · exact hroot.hOcc 651
  · exact hroot.hOcc 653
  · exact hroot.hOcc 664
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (44 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (2 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (12 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
