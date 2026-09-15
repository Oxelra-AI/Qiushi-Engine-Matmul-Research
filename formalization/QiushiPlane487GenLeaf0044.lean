import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0044Refs : Fin 49 → RowRef 668 48 := ![.occ 83, .occ 99, .occ 104, .occ 105, .occ 135, .occ 139, .occ 140, .occ 185, .occ 195, .occ 216, .occ 218, .occ 228, .occ 233, .occ 234, .occ 239, .occ 240, .occ 241, .occ 257, .occ 269, .occ 275, .occ 276, .occ 280, .occ 303, .occ 315, .occ 326, .occ 333, .occ 337, .occ 352, .occ 386, .occ 399, .occ 411, .occ 460, .occ 506, .occ 521, .occ 588, .occ 590, .occ 653, .occ 656, .occ 666, .sumGe, .nonneg 7, .nonneg 8, .nonneg 40, .branchLe 39 (0), .branchGe 23 (1), .branchGe 2 (1), .branchLe 6 (0), .branchLe 12 (0), .branchGe 14 (1)]

def plane487GenLeaf0044Mult : Fin 49 → Nat := ![291, 1650, 6519, 1596, 558, 231, 2633, 693, 327, 2805, 4473, 4255, 733, 2631, 329, 150, 755, 258, 204, 536, 354, 1869, 1296, 3324, 2408, 930, 111, 388, 3294, 279, 1170, 1488, 2967, 1806, 1638, 1239, 1197, 1155, 48, 7815, 2106, 2004, 146, 6618, 19881, 15834, 3342, 6283, 21225]

theorem plane487GenLeaf0044 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0044Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0044Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0044Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0044Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 99
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 185
  · exact hroot.hOcc 195
  · exact hroot.hOcc 216
  · exact hroot.hOcc 218
  · exact hroot.hOcc 228
  · exact hroot.hOcc 233
  · exact hroot.hOcc 234
  · exact hroot.hOcc 239
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · exact hroot.hOcc 257
  · exact hroot.hOcc 269
  · exact hroot.hOcc 275
  · exact hroot.hOcc 276
  · exact hroot.hOcc 280
  · exact hroot.hOcc 303
  · exact hroot.hOcc 315
  · exact hroot.hOcc 326
  · exact hroot.hOcc 333
  · exact hroot.hOcc 337
  · exact hroot.hOcc 352
  · exact hroot.hOcc 386
  · exact hroot.hOcc 399
  · exact hroot.hOcc 411
  · exact hroot.hOcc 460
  · exact hroot.hOcc 506
  · exact hroot.hOcc 521
  · exact hroot.hOcc 588
  · exact hroot.hOcc 590
  · exact hroot.hOcc 653
  · exact hroot.hOcc 656
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (40 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (2 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (14 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
