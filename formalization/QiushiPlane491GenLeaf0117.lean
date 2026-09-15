import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0117Refs : Fin 50 → RowRef 726 49 := ![.occ 79, .occ 88, .occ 98, .occ 105, .occ 109, .occ 111, .occ 112, .occ 144, .occ 170, .occ 171, .occ 195, .occ 198, .occ 223, .occ 234, .occ 255, .occ 257, .occ 267, .occ 275, .occ 355, .occ 377, .occ 404, .occ 418, .occ 422, .occ 524, .occ 531, .occ 543, .occ 568, .occ 573, .occ 611, .occ 612, .occ 631, .occ 640, .occ 651, .occ 652, .occ 654, .occ 671, .occ 687, .occ 689, .occ 708, .occ 712, .occ 722, .sumGe, .nonneg 32, .branchGe 31 (1), .branchGe 44 (1), .branchGe 6 (1), .branchGe 15 (1), .branchLe 13 (0), .branchLe 5 (0), .branchGe 23 (1)]

def plane491GenLeaf0117Mult : Fin 50 → Nat := ![12598, 11026, 50009, 27296, 6555, 11676, 29493, 4934, 21680, 6982, 18262, 15334, 1650, 14062, 3768, 1411, 26913, 13275, 3822, 19181, 7290, 1977, 5874, 9991, 6428, 3815, 18804, 1190, 18163, 5106, 7215, 12822, 3098, 24488, 13780, 7278, 3261, 4470, 282, 163, 6428, 53831, 5739, 144416, 129924, 84220, 21035, 37187, 52420, 161733]

theorem plane491GenLeaf0117 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0117Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0117Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0117Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0117Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 88
  · exact hroot.hOcc 98
  · exact hroot.hOcc 105
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 144
  · exact hroot.hOcc 170
  · exact hroot.hOcc 171
  · exact hroot.hOcc 195
  · exact hroot.hOcc 198
  · exact hroot.hOcc 223
  · exact hroot.hOcc 234
  · exact hroot.hOcc 255
  · exact hroot.hOcc 257
  · exact hroot.hOcc 267
  · exact hroot.hOcc 275
  · exact hroot.hOcc 355
  · exact hroot.hOcc 377
  · exact hroot.hOcc 404
  · exact hroot.hOcc 418
  · exact hroot.hOcc 422
  · exact hroot.hOcc 524
  · exact hroot.hOcc 531
  · exact hroot.hOcc 543
  · exact hroot.hOcc 568
  · exact hroot.hOcc 573
  · exact hroot.hOcc 611
  · exact hroot.hOcc 612
  · exact hroot.hOcc 631
  · exact hroot.hOcc 640
  · exact hroot.hOcc 651
  · exact hroot.hOcc 652
  · exact hroot.hOcc 654
  · exact hroot.hOcc 671
  · exact hroot.hOcc 687
  · exact hroot.hOcc 689
  · exact hroot.hOcc 708
  · exact hroot.hOcc 712
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (15 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (13 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (5 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (23 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23

end QiushiMatmul
