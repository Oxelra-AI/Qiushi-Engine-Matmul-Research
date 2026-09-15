import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0019Refs : Fin 44 → RowRef 1665 43 := ![.occ 128, .occ 131, .occ 139, .occ 511, .occ 512, .occ 515, .occ 517, .occ 521, .occ 527, .occ 641, .occ 771, .occ 781, .occ 1006, .occ 1183, .occ 1187, .occ 1281, .occ 1286, .occ 1357, .occ 1390, .occ 1400, .occ 1403, .occ 1405, .occ 1433, .occ 1489, .occ 1523, .occ 1532, .occ 1549, .occ 1571, .occ 1626, .occ 1633, .occ 1655, .occ 1658, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchGe 41 (1), .branchGe 19 (1), .branchGe 10 (1), .branchLe 0 (0)]

def plane484GenLeaf0019Mult : Fin 44 → Nat := ![30227, 5603, 18714, 28417, 21311, 34585, 44354, 14438, 7161, 1427, 4400, 25827, 2930, 4699, 21599, 21753, 743, 10046, 112, 8754, 6656, 11739, 1359, 6136, 1471, 2017, 6707, 2143, 15226, 14425, 18616, 11851, 79408, 47529, 30406, 77265, 72701, 65540, 36992, 67219, 175727, 102124, 191304, 48533]

theorem plane484GenLeaf0019 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0019Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0019Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0019Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0019Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 128
  · exact hroot.hOcc 131
  · exact hroot.hOcc 139
  · exact hroot.hOcc 511
  · exact hroot.hOcc 512
  · exact hroot.hOcc 515
  · exact hroot.hOcc 517
  · exact hroot.hOcc 521
  · exact hroot.hOcc 527
  · exact hroot.hOcc 641
  · exact hroot.hOcc 771
  · exact hroot.hOcc 781
  · exact hroot.hOcc 1006
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1281
  · exact hroot.hOcc 1286
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1390
  · exact hroot.hOcc 1400
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1523
  · exact hroot.hOcc 1532
  · exact hroot.hOcc 1549
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1633
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
