import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0046Refs : Fin 48 → RowRef 668 48 := ![.occ 99, .occ 106, .occ 110, .occ 111, .occ 122, .occ 137, .occ 169, .occ 185, .occ 194, .occ 218, .occ 219, .occ 225, .occ 228, .occ 233, .occ 234, .occ 239, .occ 246, .occ 265, .occ 294, .occ 295, .occ 296, .occ 298, .occ 303, .occ 304, .occ 313, .occ 315, .occ 326, .occ 378, .occ 379, .occ 394, .occ 399, .occ 415, .occ 471, .occ 491, .occ 503, .occ 563, .occ 588, .occ 590, .occ 623, .occ 651, .occ 657, .occ 661, .sumGe, .nonneg 19, .branchLe 39 (0), .branchGe 23 (1), .branchGe 2 (1), .branchGe 6 (1)]

def plane487GenLeaf0046Mult : Fin 48 → Nat := ![11973, 3706, 18516, 6136, 20777, 24788, 27583, 9786, 29845, 24901, 7631, 826, 9133, 2637, 45770, 42022, 4493, 2831, 9180, 12033, 4849, 5739, 10033, 3293, 8371, 17087, 4500, 5251, 1215, 7825, 5540, 23154, 4592, 17643, 14155, 402, 8646, 5445, 7390, 5410, 4996, 546, 55803, 1310, 49859, 213602, 151924, 144399]

theorem plane487GenLeaf0046 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0046Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0046Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0046Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0046Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 99
  · exact hroot.hOcc 106
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 122
  · exact hroot.hOcc 137
  · exact hroot.hOcc 169
  · exact hroot.hOcc 185
  · exact hroot.hOcc 194
  · exact hroot.hOcc 218
  · exact hroot.hOcc 219
  · exact hroot.hOcc 225
  · exact hroot.hOcc 228
  · exact hroot.hOcc 233
  · exact hroot.hOcc 234
  · exact hroot.hOcc 239
  · exact hroot.hOcc 246
  · exact hroot.hOcc 265
  · exact hroot.hOcc 294
  · exact hroot.hOcc 295
  · exact hroot.hOcc 296
  · exact hroot.hOcc 298
  · exact hroot.hOcc 303
  · exact hroot.hOcc 304
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 326
  · exact hroot.hOcc 378
  · exact hroot.hOcc 379
  · exact hroot.hOcc 394
  · exact hroot.hOcc 399
  · exact hroot.hOcc 415
  · exact hroot.hOcc 471
  · exact hroot.hOcc 491
  · exact hroot.hOcc 503
  · exact hroot.hOcc 563
  · exact hroot.hOcc 588
  · exact hroot.hOcc 590
  · exact hroot.hOcc 623
  · exact hroot.hOcc 651
  · exact hroot.hOcc 657
  · exact hroot.hOcc 661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (2 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
