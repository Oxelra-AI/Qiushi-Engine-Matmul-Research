import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0535Refs : Fin 37 → RowRef 1665 43 := ![.occ 123, .occ 125, .occ 126, .occ 135, .occ 137, .occ 171, .occ 199, .occ 224, .occ 289, .occ 295, .occ 325, .occ 471, .occ 1119, .occ 1145, .occ 1183, .occ 1200, .occ 1292, .occ 1300, .occ 1343, .occ 1446, .occ 1480, .occ 1481, .occ 1492, .occ 1571, .occ 1573, .occ 1638, .occ 1642, .occ 1643, .occ 1644, .sumGe, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchGe 30 (1), .branchLe 1 (0), .branchLe 0 (0), .branchGe 2 (1)]

def plane484GenLeaf0535Mult : Fin 37 → Nat := ![143, 4, 6, 8, 56, 46, 2, 4, 2, 194, 95, 25, 25, 35, 91, 64, 22, 22, 2, 2, 23, 91, 49, 62, 47, 51, 4, 14, 4, 216, 244, 396, 44, 444, 216, 216, 658]

theorem plane484GenLeaf0535 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0535Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0535Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0535Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0535Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 171
  · exact hroot.hOcc 199
  · exact hroot.hOcc 224
  · exact hroot.hOcc 289
  · exact hroot.hOcc 295
  · exact hroot.hOcc 325
  · exact hroot.hOcc 471
  · exact hroot.hOcc 1119
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1292
  · exact hroot.hOcc 1300
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1446
  · exact hroot.hOcc 1480
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1642
  · exact hroot.hOcc 1643
  · exact hroot.hOcc 1644
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
