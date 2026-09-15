import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0059Refs : Fin 50 → RowRef 726 49 := ![.occ 78, .occ 100, .occ 102, .occ 103, .occ 106, .occ 110, .occ 113, .occ 119, .occ 133, .occ 162, .occ 164, .occ 181, .occ 219, .occ 220, .occ 293, .occ 299, .occ 320, .occ 324, .occ 326, .occ 332, .occ 341, .occ 343, .occ 368, .occ 407, .occ 422, .occ 424, .occ 431, .occ 461, .occ 485, .occ 509, .occ 511, .occ 515, .occ 548, .occ 563, .occ 632, .occ 648, .occ 653, .occ 665, .occ 709, .occ 715, .occ 722, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchGe 11 (1), .branchLe 44 (0), .branchLe 46 (0), .branchLe 18 (0), .branchLe 25 (0)]

def plane491GenLeaf0059Mult : Fin 50 → Nat := ![5019, 40438, 1514, 17191, 13602, 2508, 3525, 1877, 9266, 4039, 271, 10351, 13308, 4952, 11889, 653, 2333, 4592, 7007, 528, 7836, 9851, 14310, 1557, 2224, 11572, 8595, 1942, 3780, 1895, 6441, 6371, 745, 5626, 14881, 2974, 9681, 6799, 2908, 3830, 11641, 43412, 18345, 42884, 115614, 79093, 16411, 36613, 24452, 40504]

theorem plane491GenLeaf0059 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0059Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0059Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0059Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0059Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 119
  · exact hroot.hOcc 133
  · exact hroot.hOcc 162
  · exact hroot.hOcc 164
  · exact hroot.hOcc 181
  · exact hroot.hOcc 219
  · exact hroot.hOcc 220
  · exact hroot.hOcc 293
  · exact hroot.hOcc 299
  · exact hroot.hOcc 320
  · exact hroot.hOcc 324
  · exact hroot.hOcc 326
  · exact hroot.hOcc 332
  · exact hroot.hOcc 341
  · exact hroot.hOcc 343
  · exact hroot.hOcc 368
  · exact hroot.hOcc 407
  · exact hroot.hOcc 422
  · exact hroot.hOcc 424
  · exact hroot.hOcc 431
  · exact hroot.hOcc 461
  · exact hroot.hOcc 485
  · exact hroot.hOcc 509
  · exact hroot.hOcc 511
  · exact hroot.hOcc 515
  · exact hroot.hOcc 548
  · exact hroot.hOcc 563
  · exact hroot.hOcc 632
  · exact hroot.hOcc 648
  · exact hroot.hOcc 653
  · exact hroot.hOcc 665
  · exact hroot.hOcc 709
  · exact hroot.hOcc 715
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (18 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (25 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25

end QiushiMatmul
