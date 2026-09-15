import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0528Refs : Fin 42 → RowRef 1665 43 := ![.occ 125, .occ 127, .occ 130, .occ 133, .occ 138, .occ 142, .occ 221, .occ 296, .occ 380, .occ 573, .occ 691, .occ 713, .occ 735, .occ 766, .occ 767, .occ 768, .occ 787, .occ 1043, .occ 1046, .occ 1206, .occ 1208, .occ 1298, .occ 1378, .occ 1392, .occ 1412, .occ 1449, .occ 1467, .occ 1483, .occ 1559, .occ 1606, .occ 1611, .occ 1637, .sumGe, .nonneg 26, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 30 (0), .branchGe 34 (1), .branchGe 9 (1), .branchLe 3 (0), .branchGe 42 (1)]

def plane484GenLeaf0528Mult : Fin 42 → Nat := ![19, 15, 99, 33, 85, 67, 214, 114, 29, 26, 62, 186, 40, 187, 125, 3, 95, 18, 69, 43, 1, 24, 39, 18, 37, 13, 170, 66, 34, 2, 94, 92, 262, 18, 780, 816, 138, 261, 485, 960, 129, 992]

theorem plane484GenLeaf0528 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0528Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0528Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0528Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0528Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 221
  · exact hroot.hOcc 296
  · exact hroot.hOcc 380
  · exact hroot.hOcc 573
  · exact hroot.hOcc 691
  · exact hroot.hOcc 713
  · exact hroot.hOcc 735
  · exact hroot.hOcc 766
  · exact hroot.hOcc 767
  · exact hroot.hOcc 768
  · exact hroot.hOcc 787
  · exact hroot.hOcc 1043
  · exact hroot.hOcc 1046
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1298
  · exact hroot.hOcc 1378
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1412
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1559
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1611
  · exact hroot.hOcc 1637
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
