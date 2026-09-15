import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0065Refs : Fin 49 → RowRef 726 49 := ![.occ 85, .occ 99, .occ 101, .occ 103, .occ 106, .occ 111, .occ 117, .occ 120, .occ 129, .occ 220, .occ 222, .occ 251, .occ 252, .occ 255, .occ 256, .occ 257, .occ 258, .occ 304, .occ 312, .occ 319, .occ 343, .occ 363, .occ 368, .occ 385, .occ 386, .occ 407, .occ 430, .occ 431, .occ 447, .occ 489, .occ 532, .occ 546, .occ 563, .occ 576, .occ 583, .occ 586, .occ 620, .occ 712, .occ 716, .occ 722, .sumGe, .nonneg 19, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchGe 11 (1), .branchGe 44 (1), .branchLe 6 (0), .branchGe 3 (1)]

def plane491GenLeaf0065Mult : Fin 49 → Nat := ![123, 295, 12, 257, 223, 184, 140, 46, 142, 130, 564, 870, 54, 241, 26, 334, 529, 437, 378, 56, 211, 396, 54, 26, 169, 35, 220, 35, 68, 54, 35, 54, 123, 88, 334, 448, 35, 307, 88, 352, 1135, 192, 317, 746, 1130, 1387, 3566, 587, 4445]

theorem plane491GenLeaf0065 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0065Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0065Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0065Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0065Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 99
  · exact hroot.hOcc 101
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 111
  · exact hroot.hOcc 117
  · exact hroot.hOcc 120
  · exact hroot.hOcc 129
  · exact hroot.hOcc 220
  · exact hroot.hOcc 222
  · exact hroot.hOcc 251
  · exact hroot.hOcc 252
  · exact hroot.hOcc 255
  · exact hroot.hOcc 256
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 304
  · exact hroot.hOcc 312
  · exact hroot.hOcc 319
  · exact hroot.hOcc 343
  · exact hroot.hOcc 363
  · exact hroot.hOcc 368
  · exact hroot.hOcc 385
  · exact hroot.hOcc 386
  · exact hroot.hOcc 407
  · exact hroot.hOcc 430
  · exact hroot.hOcc 431
  · exact hroot.hOcc 447
  · exact hroot.hOcc 489
  · exact hroot.hOcc 532
  · exact hroot.hOcc 546
  · exact hroot.hOcc 563
  · exact hroot.hOcc 576
  · exact hroot.hOcc 583
  · exact hroot.hOcc 586
  · exact hroot.hOcc 620
  · exact hroot.hOcc 712
  · exact hroot.hOcc 716
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (3 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
