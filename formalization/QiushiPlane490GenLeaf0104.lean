import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0104Refs : Fin 44 → RowRef 713 43 := ![.occ 87, .occ 89, .occ 90, .occ 105, .occ 108, .occ 109, .occ 131, .occ 152, .occ 159, .occ 188, .occ 196, .occ 231, .occ 250, .occ 272, .occ 283, .occ 303, .occ 317, .occ 321, .occ 362, .occ 447, .occ 448, .occ 449, .occ 456, .occ 480, .occ 481, .occ 521, .occ 542, .occ 582, .occ 602, .occ 613, .occ 632, .occ 653, .occ 666, .occ 683, .occ 694, .occ 712, .sumGe, .branchGe 29 (1), .branchGe 18 (1), .branchLe 14 (0), .branchGe 1 (1), .branchLe 20 (0), .branchGe 15 (1), .branchLe 31 (0)]

def plane490GenLeaf0104Mult : Fin 44 → Nat := ![712, 700, 151, 2697, 2968, 1958, 1570, 1308, 1868, 718, 287, 413, 1302, 293, 1298, 2275, 1218, 298, 1231, 879, 680, 124, 60, 1069, 232, 169, 589, 363, 786, 105, 1307, 869, 293, 71, 324, 1209, 4270, 11358, 5904, 4146, 1057, 3357, 10423, 2192]

theorem plane490GenLeaf0104 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0104Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0104Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0104Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0104Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 131
  · exact hroot.hOcc 152
  · exact hroot.hOcc 159
  · exact hroot.hOcc 188
  · exact hroot.hOcc 196
  · exact hroot.hOcc 231
  · exact hroot.hOcc 250
  · exact hroot.hOcc 272
  · exact hroot.hOcc 283
  · exact hroot.hOcc 303
  · exact hroot.hOcc 317
  · exact hroot.hOcc 321
  · exact hroot.hOcc 362
  · exact hroot.hOcc 447
  · exact hroot.hOcc 448
  · exact hroot.hOcc 449
  · exact hroot.hOcc 456
  · exact hroot.hOcc 480
  · exact hroot.hOcc 481
  · exact hroot.hOcc 521
  · exact hroot.hOcc 542
  · exact hroot.hOcc 582
  · exact hroot.hOcc 602
  · exact hroot.hOcc 613
  · exact hroot.hOcc 632
  · exact hroot.hOcc 653
  · exact hroot.hOcc 666
  · exact hroot.hOcc 683
  · exact hroot.hOcc 694
  · exact hroot.hOcc 712
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31

end QiushiMatmul
