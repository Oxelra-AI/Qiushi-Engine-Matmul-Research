import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0094Refs : Fin 41 → RowRef 713 43 := ![.occ 102, .occ 103, .occ 105, .occ 106, .occ 108, .occ 109, .occ 124, .occ 125, .occ 154, .occ 168, .occ 170, .occ 186, .occ 198, .occ 201, .occ 217, .occ 248, .occ 250, .occ 299, .occ 321, .occ 336, .occ 338, .occ 340, .occ 354, .occ 437, .occ 501, .occ 504, .occ 521, .occ 542, .occ 567, .occ 599, .occ 606, .occ 632, .occ 675, .occ 703, .occ 709, .occ 711, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchGe 12 (1), .branchLe 2 (0)]

def plane490GenLeaf0094Mult : Fin 41 → Nat := ![110, 3306, 4295, 1457, 1780, 1125, 167, 180, 977, 282, 2869, 110, 2437, 372, 1583, 110, 1148, 2032, 110, 1739, 359, 404, 820, 380, 55, 2108, 1553, 173, 1113, 266, 268, 55, 986, 330, 1156, 224, 4405, 14627, 4405, 18528, 4405]

theorem plane490GenLeaf0094 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0094Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0094Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0094Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0094Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 154
  · exact hroot.hOcc 168
  · exact hroot.hOcc 170
  · exact hroot.hOcc 186
  · exact hroot.hOcc 198
  · exact hroot.hOcc 201
  · exact hroot.hOcc 217
  · exact hroot.hOcc 248
  · exact hroot.hOcc 250
  · exact hroot.hOcc 299
  · exact hroot.hOcc 321
  · exact hroot.hOcc 336
  · exact hroot.hOcc 338
  · exact hroot.hOcc 340
  · exact hroot.hOcc 354
  · exact hroot.hOcc 437
  · exact hroot.hOcc 501
  · exact hroot.hOcc 504
  · exact hroot.hOcc 521
  · exact hroot.hOcc 542
  · exact hroot.hOcc 567
  · exact hroot.hOcc 599
  · exact hroot.hOcc 606
  · exact hroot.hOcc 632
  · exact hroot.hOcc 675
  · exact hroot.hOcc 703
  · exact hroot.hOcc 709
  · exact hroot.hOcc 711
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2

end QiushiMatmul
