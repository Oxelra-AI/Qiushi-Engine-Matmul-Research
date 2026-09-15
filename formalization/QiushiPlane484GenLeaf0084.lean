import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0084Refs : Fin 41 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 130, .occ 265, .occ 569, .occ 728, .occ 742, .occ 747, .occ 766, .occ 767, .occ 788, .occ 860, .occ 960, .occ 1094, .occ 1096, .occ 1226, .occ 1228, .occ 1257, .occ 1320, .occ 1321, .occ 1369, .occ 1390, .occ 1392, .occ 1406, .occ 1414, .occ 1415, .occ 1420, .occ 1462, .occ 1489, .occ 1606, .sumGe, .nonneg 3, .nonneg 5, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchGe 42 (1), .branchGe 9 (1), .branchGe 37 (1)]

def plane484GenLeaf0084Mult : Fin 41 → Nat := ![43, 6, 33, 7, 15, 5, 17, 8, 4, 28, 34, 5, 3, 2, 13, 7, 5, 5, 4, 2, 12, 30, 12, 7, 16, 12, 10, 7, 15, 22, 55, 101, 5, 55, 34, 50, 22, 138, 184, 231, 170]

theorem plane484GenLeaf0084 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0084Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0084Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0084Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0084Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 130
  · exact hroot.hOcc 265
  · exact hroot.hOcc 569
  · exact hroot.hOcc 728
  · exact hroot.hOcc 742
  · exact hroot.hOcc 747
  · exact hroot.hOcc 766
  · exact hroot.hOcc 767
  · exact hroot.hOcc 788
  · exact hroot.hOcc 860
  · exact hroot.hOcc 960
  · exact hroot.hOcc 1094
  · exact hroot.hOcc 1096
  · exact hroot.hOcc 1226
  · exact hroot.hOcc 1228
  · exact hroot.hOcc 1257
  · exact hroot.hOcc 1320
  · exact hroot.hOcc 1321
  · exact hroot.hOcc 1369
  · exact hroot.hOcc 1390
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1406
  · exact hroot.hOcc 1414
  · exact hroot.hOcc 1415
  · exact hroot.hOcc 1420
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1606
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
