import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0081Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 94, .occ 99, .occ 100, .occ 105, .occ 161, .occ 217, .occ 219, .occ 227, .occ 237, .occ 240, .occ 241, .occ 266, .occ 303, .occ 305, .occ 313, .occ 315, .occ 322, .occ 332, .occ 343, .occ 376, .occ 377, .occ 379, .occ 380, .occ 399, .occ 401, .occ 443, .occ 451, .occ 501, .occ 521, .occ 544, .occ 545, .occ 546, .occ 617, .occ 653, .occ 661, .occ 662, .occ 665, .occ 666, .sumGe, .nonneg 8, .nonneg 43, .branchGe 39 (1), .branchLe 7 (0), .branchGe 28 (1), .branchLe 3 (0), .branchLe 36 (0), .branchLe 35 (0), .branchGe 13 (1)]

def plane487GenLeaf0081Mult : Fin 49 → Nat := ![10170, 212, 2035, 4404, 10107, 3323, 531, 11439, 3125, 1365, 29244, 4637, 5759, 15, 5784, 6137, 4925, 11013, 8534, 109, 4727, 12160, 8867, 14478, 3015, 13523, 14509, 7079, 6124, 168, 16008, 586, 1834, 3796, 8955, 12325, 1678, 3091, 7946, 44489, 7810, 2591, 61372, 6931, 98308, 34865, 41182, 20891, 108114]

theorem plane487GenLeaf0081 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0081Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0081Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0081Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0081Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 94
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 105
  · exact hroot.hOcc 161
  · exact hroot.hOcc 217
  · exact hroot.hOcc 219
  · exact hroot.hOcc 227
  · exact hroot.hOcc 237
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · exact hroot.hOcc 266
  · exact hroot.hOcc 303
  · exact hroot.hOcc 305
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 322
  · exact hroot.hOcc 332
  · exact hroot.hOcc 343
  · exact hroot.hOcc 376
  · exact hroot.hOcc 377
  · exact hroot.hOcc 379
  · exact hroot.hOcc 380
  · exact hroot.hOcc 399
  · exact hroot.hOcc 401
  · exact hroot.hOcc 443
  · exact hroot.hOcc 451
  · exact hroot.hOcc 501
  · exact hroot.hOcc 521
  · exact hroot.hOcc 544
  · exact hroot.hOcc 545
  · exact hroot.hOcc 546
  · exact hroot.hOcc 617
  · exact hroot.hOcc 653
  · exact hroot.hOcc 661
  · exact hroot.hOcc 662
  · exact hroot.hOcc 665
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (43 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (3 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (35 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (13 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
