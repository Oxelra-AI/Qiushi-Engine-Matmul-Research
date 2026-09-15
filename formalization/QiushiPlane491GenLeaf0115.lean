import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0115Refs : Fin 50 → RowRef 726 49 := ![.occ 79, .occ 98, .occ 107, .occ 111, .occ 124, .occ 175, .occ 179, .occ 234, .occ 257, .occ 287, .occ 293, .occ 302, .occ 318, .occ 355, .occ 363, .occ 372, .occ 393, .occ 421, .occ 422, .occ 423, .occ 430, .occ 462, .occ 473, .occ 495, .occ 531, .occ 542, .occ 573, .occ 607, .occ 631, .occ 640, .occ 652, .occ 653, .occ 654, .occ 662, .occ 671, .occ 691, .occ 713, .occ 714, .occ 725, .sumGe, .nonneg 33, .branchGe 31 (1), .branchGe 44 (1), .branchGe 6 (1), .branchGe 15 (1), .branchLe 13 (0), .branchLe 5 (0), .branchLe 23 (0), .branchLe 27 (0), .branchGe 42 (1)]

def plane491GenLeaf0115Mult : Fin 50 → Nat := ![24796, 83095, 124950, 36899, 13559, 60770, 29229, 22721, 68920, 11365, 31090, 9362, 35394, 23194, 17526, 8763, 14112, 13124, 62465, 3850, 4587, 1921, 16340, 52342, 58862, 25534, 16105, 19289, 47421, 22066, 34821, 26212, 1670, 46322, 15939, 23113, 5592, 9719, 15786, 164567, 60446, 302437, 264186, 110571, 231024, 96168, 12651, 146958, 120829, 430172]

theorem plane491GenLeaf0115 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0115Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0115Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0115Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0115Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 98
  · exact hroot.hOcc 107
  · exact hroot.hOcc 111
  · exact hroot.hOcc 124
  · exact hroot.hOcc 175
  · exact hroot.hOcc 179
  · exact hroot.hOcc 234
  · exact hroot.hOcc 257
  · exact hroot.hOcc 287
  · exact hroot.hOcc 293
  · exact hroot.hOcc 302
  · exact hroot.hOcc 318
  · exact hroot.hOcc 355
  · exact hroot.hOcc 363
  · exact hroot.hOcc 372
  · exact hroot.hOcc 393
  · exact hroot.hOcc 421
  · exact hroot.hOcc 422
  · exact hroot.hOcc 423
  · exact hroot.hOcc 430
  · exact hroot.hOcc 462
  · exact hroot.hOcc 473
  · exact hroot.hOcc 495
  · exact hroot.hOcc 531
  · exact hroot.hOcc 542
  · exact hroot.hOcc 573
  · exact hroot.hOcc 607
  · exact hroot.hOcc 631
  · exact hroot.hOcc 640
  · exact hroot.hOcc 652
  · exact hroot.hOcc 653
  · exact hroot.hOcc 654
  · exact hroot.hOcc 662
  · exact hroot.hOcc 671
  · exact hroot.hOcc 691
  · exact hroot.hOcc 713
  · exact hroot.hOcc 714
  · exact hroot.hOcc 725
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (15 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (13 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (5 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (42 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
