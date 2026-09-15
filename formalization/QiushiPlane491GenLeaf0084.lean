import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0084Refs : Fin 49 → RowRef 726 49 := ![.occ 98, .occ 100, .occ 102, .occ 110, .occ 118, .occ 126, .occ 151, .occ 167, .occ 219, .occ 230, .occ 232, .occ 234, .occ 244, .occ 255, .occ 309, .occ 315, .occ 350, .occ 359, .occ 393, .occ 409, .occ 410, .occ 411, .occ 421, .occ 424, .occ 431, .occ 489, .occ 493, .occ 506, .occ 518, .occ 538, .occ 546, .occ 567, .occ 622, .occ 640, .occ 642, .occ 644, .occ 671, .occ 673, .occ 708, .sumGe, .nonneg 10, .nonneg 37, .branchGe 31 (1), .branchLe 44 (0), .branchLe 11 (0), .branchGe 27 (1), .branchLe 43 (0), .branchLe 17 (0), .branchGe 2 (1)]

def plane491GenLeaf0084Mult : Fin 49 → Nat := ![394, 7548, 1686, 6571, 83, 6689, 1173, 1639, 2555, 2534, 3093, 4514, 437, 9, 864, 1343, 2287, 10355, 4070, 407, 1343, 778, 668, 3402, 3725, 2680, 829, 135, 2065, 1835, 384, 281, 3683, 50, 330, 1724, 5786, 1435, 2292, 12977, 2354, 503, 25738, 11483, 10297, 21206, 5913, 12927, 40714]

theorem plane491GenLeaf0084 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0084Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0084Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0084Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0084Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 110
  · exact hroot.hOcc 118
  · exact hroot.hOcc 126
  · exact hroot.hOcc 151
  · exact hroot.hOcc 167
  · exact hroot.hOcc 219
  · exact hroot.hOcc 230
  · exact hroot.hOcc 232
  · exact hroot.hOcc 234
  · exact hroot.hOcc 244
  · exact hroot.hOcc 255
  · exact hroot.hOcc 309
  · exact hroot.hOcc 315
  · exact hroot.hOcc 350
  · exact hroot.hOcc 359
  · exact hroot.hOcc 393
  · exact hroot.hOcc 409
  · exact hroot.hOcc 410
  · exact hroot.hOcc 411
  · exact hroot.hOcc 421
  · exact hroot.hOcc 424
  · exact hroot.hOcc 431
  · exact hroot.hOcc 489
  · exact hroot.hOcc 493
  · exact hroot.hOcc 506
  · exact hroot.hOcc 518
  · exact hroot.hOcc 538
  · exact hroot.hOcc 546
  · exact hroot.hOcc 567
  · exact hroot.hOcc 622
  · exact hroot.hOcc 640
  · exact hroot.hOcc 642
  · exact hroot.hOcc 644
  · exact hroot.hOcc 671
  · exact hroot.hOcc 673
  · exact hroot.hOcc 708
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (37 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (17 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (2 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
