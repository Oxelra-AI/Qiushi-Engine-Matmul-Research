import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0079Refs : Fin 50 → RowRef 726 49 := ![.occ 87, .occ 92, .occ 98, .occ 118, .occ 122, .occ 123, .occ 149, .occ 167, .occ 230, .occ 234, .occ 243, .occ 276, .occ 334, .occ 335, .occ 355, .occ 359, .occ 373, .occ 379, .occ 393, .occ 410, .occ 423, .occ 425, .occ 428, .occ 431, .occ 482, .occ 501, .occ 548, .occ 594, .occ 610, .occ 611, .occ 621, .occ 625, .occ 662, .occ 669, .occ 685, .occ 687, .occ 691, .occ 705, .occ 714, .occ 725, .sumGe, .nonneg 35, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchLe 27 (0), .branchGe 22 (1), .branchLe 3 (0), .branchLe 23 (0), .branchLe 8 (0)]

def plane491GenLeaf0079Mult : Fin 50 → Nat := ![2751702, 1002323, 2981561, 1376878, 799306, 2313355, 750198, 1158680, 703668, 1271111, 287522, 352807, 687843, 551583, 219352, 893735, 425253, 1364778, 1208044, 264412, 1495021, 349147, 143971, 33728, 310665, 362819, 18445, 85982, 372665, 540431, 593245, 263768, 1288056, 549438, 747722, 562124, 371826, 218358, 155316, 351187, 3870061, 407821, 12240262, 3279877, 2099879, 3329630, 7572368, 3320623, 2736385, 2979261]

theorem plane491GenLeaf0079 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0079Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0079Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0079Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0079Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 92
  · exact hroot.hOcc 98
  · exact hroot.hOcc 118
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 149
  · exact hroot.hOcc 167
  · exact hroot.hOcc 230
  · exact hroot.hOcc 234
  · exact hroot.hOcc 243
  · exact hroot.hOcc 276
  · exact hroot.hOcc 334
  · exact hroot.hOcc 335
  · exact hroot.hOcc 355
  · exact hroot.hOcc 359
  · exact hroot.hOcc 373
  · exact hroot.hOcc 379
  · exact hroot.hOcc 393
  · exact hroot.hOcc 410
  · exact hroot.hOcc 423
  · exact hroot.hOcc 425
  · exact hroot.hOcc 428
  · exact hroot.hOcc 431
  · exact hroot.hOcc 482
  · exact hroot.hOcc 501
  · exact hroot.hOcc 548
  · exact hroot.hOcc 594
  · exact hroot.hOcc 610
  · exact hroot.hOcc 611
  · exact hroot.hOcc 621
  · exact hroot.hOcc 625
  · exact hroot.hOcc 662
  · exact hroot.hOcc 669
  · exact hroot.hOcc 685
  · exact hroot.hOcc 687
  · exact hroot.hOcc 691
  · exact hroot.hOcc 705
  · exact hroot.hOcc 714
  · exact hroot.hOcc 725
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (35 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (22 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (3 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (8 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8

end QiushiMatmul
