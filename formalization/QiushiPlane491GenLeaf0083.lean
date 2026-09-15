import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0083Refs : Fin 50 → RowRef 726 49 := ![.occ 83, .occ 85, .occ 98, .occ 100, .occ 106, .occ 118, .occ 122, .occ 151, .occ 153, .occ 161, .occ 164, .occ 170, .occ 222, .occ 232, .occ 323, .occ 335, .occ 350, .occ 393, .occ 409, .occ 410, .occ 421, .occ 424, .occ 482, .occ 484, .occ 485, .occ 486, .occ 527, .occ 529, .occ 565, .occ 567, .occ 590, .occ 601, .occ 606, .occ 611, .occ 619, .occ 634, .occ 653, .occ 662, .occ 665, .occ 679, .occ 684, .occ 716, .sumGe, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchGe 27 (1), .branchLe 43 (0), .branchLe 17 (0), .branchLe 2 (0)]

def plane491GenLeaf0083Mult : Fin 50 → Nat := ![4432, 38765, 48054, 130895, 105823, 129019, 15254, 32156, 34853, 58546, 98702, 10658, 503, 7399, 77603, 39483, 63642, 104559, 14846, 36611, 28080, 37016, 26644, 45354, 58839, 18710, 1097, 26820, 22591, 73516, 6922, 46431, 19549, 66249, 1775, 17995, 3515, 50671, 26412, 27451, 3149, 18931, 231539, 653875, 212608, 180868, 806172, 228024, 89883, 178075]

theorem plane491GenLeaf0083 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0083Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0083Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0083Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0083Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 85
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 106
  · exact hroot.hOcc 118
  · exact hroot.hOcc 122
  · exact hroot.hOcc 151
  · exact hroot.hOcc 153
  · exact hroot.hOcc 161
  · exact hroot.hOcc 164
  · exact hroot.hOcc 170
  · exact hroot.hOcc 222
  · exact hroot.hOcc 232
  · exact hroot.hOcc 323
  · exact hroot.hOcc 335
  · exact hroot.hOcc 350
  · exact hroot.hOcc 393
  · exact hroot.hOcc 409
  · exact hroot.hOcc 410
  · exact hroot.hOcc 421
  · exact hroot.hOcc 424
  · exact hroot.hOcc 482
  · exact hroot.hOcc 484
  · exact hroot.hOcc 485
  · exact hroot.hOcc 486
  · exact hroot.hOcc 527
  · exact hroot.hOcc 529
  · exact hroot.hOcc 565
  · exact hroot.hOcc 567
  · exact hroot.hOcc 590
  · exact hroot.hOcc 601
  · exact hroot.hOcc 606
  · exact hroot.hOcc 611
  · exact hroot.hOcc 619
  · exact hroot.hOcc 634
  · exact hroot.hOcc 653
  · exact hroot.hOcc 662
  · exact hroot.hOcc 665
  · exact hroot.hOcc 679
  · exact hroot.hOcc 684
  · exact hroot.hOcc 716
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (17 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (2 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2

end QiushiMatmul
