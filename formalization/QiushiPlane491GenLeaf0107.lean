import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0107Refs : Fin 50 → RowRef 726 49 := ![.occ 98, .occ 99, .occ 103, .occ 105, .occ 109, .occ 112, .occ 124, .occ 169, .occ 170, .occ 212, .occ 219, .occ 220, .occ 234, .occ 258, .occ 284, .occ 319, .occ 328, .occ 329, .occ 334, .occ 341, .occ 367, .occ 404, .occ 421, .occ 495, .occ 531, .occ 532, .occ 541, .occ 543, .occ 563, .occ 565, .occ 566, .occ 567, .occ 582, .occ 585, .occ 607, .occ 614, .occ 630, .occ 662, .occ 686, .occ 691, .occ 707, .occ 709, .occ 722, .sumGe, .branchGe 31 (1), .branchGe 44 (1), .branchLe 6 (0), .branchGe 39 (1), .branchLe 27 (0), .branchGe 11 (1)]

def plane491GenLeaf0107Mult : Fin 50 → Nat := ![233255, 134056, 249503, 30174, 141655, 110494, 115710, 73218, 67016, 3089, 34129, 9356, 35149, 3266, 86715, 123329, 31402, 47075, 30309, 39040, 65985, 115271, 19971, 138143, 48845, 39548, 20818, 27358, 6560, 4416, 64925, 10913, 20636, 36092, 30352, 24010, 21974, 117672, 19752, 39930, 35348, 20534, 44486, 320835, 795009, 660449, 255135, 128581, 224084, 847753]

theorem plane491GenLeaf0107 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0107Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0107Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0107Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0107Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 124
  · exact hroot.hOcc 169
  · exact hroot.hOcc 170
  · exact hroot.hOcc 212
  · exact hroot.hOcc 219
  · exact hroot.hOcc 220
  · exact hroot.hOcc 234
  · exact hroot.hOcc 258
  · exact hroot.hOcc 284
  · exact hroot.hOcc 319
  · exact hroot.hOcc 328
  · exact hroot.hOcc 329
  · exact hroot.hOcc 334
  · exact hroot.hOcc 341
  · exact hroot.hOcc 367
  · exact hroot.hOcc 404
  · exact hroot.hOcc 421
  · exact hroot.hOcc 495
  · exact hroot.hOcc 531
  · exact hroot.hOcc 532
  · exact hroot.hOcc 541
  · exact hroot.hOcc 543
  · exact hroot.hOcc 563
  · exact hroot.hOcc 565
  · exact hroot.hOcc 566
  · exact hroot.hOcc 567
  · exact hroot.hOcc 582
  · exact hroot.hOcc 585
  · exact hroot.hOcc 607
  · exact hroot.hOcc 614
  · exact hroot.hOcc 630
  · exact hroot.hOcc 662
  · exact hroot.hOcc 686
  · exact hroot.hOcc 691
  · exact hroot.hOcc 707
  · exact hroot.hOcc 709
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (39 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
