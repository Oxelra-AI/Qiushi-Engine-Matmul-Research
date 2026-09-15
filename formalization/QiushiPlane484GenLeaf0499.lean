import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0499Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 136, .occ 138, .occ 140, .occ 141, .occ 142, .occ 330, .occ 516, .occ 635, .occ 683, .occ 693, .occ 700, .occ 783, .occ 843, .occ 854, .occ 1166, .occ 1174, .occ 1183, .occ 1191, .occ 1258, .occ 1292, .occ 1330, .occ 1334, .occ 1343, .occ 1358, .occ 1365, .occ 1470, .occ 1530, .occ 1532, .occ 1564, .occ 1570, .occ 1590, .occ 1647, .sumGe, .nonneg 21, .branchGe 15 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 32 (0), .branchLe 14 (0), .branchGe 36 (1), .branchGe 28 (1), .branchGe 38 (1)]

def plane484GenLeaf0499Mult : Fin 44 → Nat := ![1516, 8268, 217, 15022, 1802, 107, 1119, 1762, 5893, 464, 13197, 3174, 576, 20060, 9212, 54, 3334, 3463, 3833, 54, 312, 11675, 9945, 1257, 336, 3753, 8527, 58, 811, 1810, 5616, 603, 6527, 389, 20118, 998, 84833, 7186, 73152, 12902, 11202, 29667, 24402, 60820]

theorem plane484GenLeaf0499 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0499Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0499Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0499Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0499Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 330
  · exact hroot.hOcc 516
  · exact hroot.hOcc 635
  · exact hroot.hOcc 683
  · exact hroot.hOcc 693
  · exact hroot.hOcc 700
  · exact hroot.hOcc 783
  · exact hroot.hOcc 843
  · exact hroot.hOcc 854
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1292
  · exact hroot.hOcc 1330
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1365
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1530
  · exact hroot.hOcc 1532
  · exact hroot.hOcc 1564
  · exact hroot.hOcc 1570
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1647
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
