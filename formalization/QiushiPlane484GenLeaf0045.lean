import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0045Refs : Fin 40 → RowRef 1665 43 := ![.occ 98, .occ 120, .occ 128, .occ 132, .occ 137, .occ 152, .occ 202, .occ 343, .occ 421, .occ 614, .occ 795, .occ 1146, .occ 1158, .occ 1308, .occ 1314, .occ 1342, .occ 1347, .occ 1368, .occ 1382, .occ 1421, .occ 1472, .occ 1517, .occ 1518, .occ 1524, .occ 1553, .occ 1561, .occ 1609, .occ 1610, .occ 1626, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchGe 17 (1), .branchLe 7 (0), .branchLe 18 (0), .branchLe 1 (0), .branchGe 5 (1)]

def plane484GenLeaf0045Mult : Fin 40 → Nat := ![63, 131, 1566, 328, 619, 1036, 533, 260, 396, 1777, 674, 328, 642, 286, 267, 235, 328, 583, 411, 38, 656, 557, 506, 746, 103, 122, 304, 700, 1261, 3366, 2724, 642, 3206, 3366, 3366, 7187, 3366, 773, 1144, 8159]

theorem plane484GenLeaf0045 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0045Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0045Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0045Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0045Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 98
  · exact hroot.hOcc 120
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 152
  · exact hroot.hOcc 202
  · exact hroot.hOcc 343
  · exact hroot.hOcc 421
  · exact hroot.hOcc 614
  · exact hroot.hOcc 795
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1308
  · exact hroot.hOcc 1314
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1347
  · exact hroot.hOcc 1368
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1421
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1518
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1553
  · exact hroot.hOcc 1561
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1626
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
