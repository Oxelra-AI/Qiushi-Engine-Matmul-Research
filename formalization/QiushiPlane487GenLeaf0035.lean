import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0035Refs : Fin 49 → RowRef 668 48 := ![.occ 82, .occ 83, .occ 89, .occ 93, .occ 95, .occ 110, .occ 111, .occ 118, .occ 119, .occ 120, .occ 148, .occ 153, .occ 218, .occ 294, .occ 296, .occ 312, .occ 321, .occ 343, .occ 347, .occ 356, .occ 377, .occ 386, .occ 390, .occ 392, .occ 434, .occ 435, .occ 469, .occ 471, .occ 476, .occ 490, .occ 523, .occ 539, .occ 562, .occ 566, .occ 593, .occ 633, .occ 639, .occ 642, .sumGe, .nonneg 8, .nonneg 25, .nonneg 45, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchGe 33 (1), .branchGe 12 (1), .branchLe 19 (0), .branchLe 17 (0)]

def plane487GenLeaf0035Mult : Fin 49 → Nat := ![741, 258, 1145, 523, 269, 147, 311, 139, 1136, 609, 751, 626, 292, 169, 1142, 1095, 227, 35, 299, 78, 485, 82, 129, 194, 444, 1102, 470, 311, 1493, 766, 659, 129, 667, 297, 72, 972, 10, 173, 2413, 2517, 46, 806, 2378, 791, 6921, 9053, 6518, 2230, 1569]

theorem plane487GenLeaf0035 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0035Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0035Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0035Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0035Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 89
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 148
  · exact hroot.hOcc 153
  · exact hroot.hOcc 218
  · exact hroot.hOcc 294
  · exact hroot.hOcc 296
  · exact hroot.hOcc 312
  · exact hroot.hOcc 321
  · exact hroot.hOcc 343
  · exact hroot.hOcc 347
  · exact hroot.hOcc 356
  · exact hroot.hOcc 377
  · exact hroot.hOcc 386
  · exact hroot.hOcc 390
  · exact hroot.hOcc 392
  · exact hroot.hOcc 434
  · exact hroot.hOcc 435
  · exact hroot.hOcc 469
  · exact hroot.hOcc 471
  · exact hroot.hOcc 476
  · exact hroot.hOcc 490
  · exact hroot.hOcc 523
  · exact hroot.hOcc 539
  · exact hroot.hOcc 562
  · exact hroot.hOcc 566
  · exact hroot.hOcc 593
  · exact hroot.hOcc 633
  · exact hroot.hOcc 639
  · exact hroot.hOcc 642
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (25 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (45 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (12 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (17 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17

end QiushiMatmul
