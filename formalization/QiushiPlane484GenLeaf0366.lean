import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0366Refs : Fin 44 → RowRef 1665 43 := ![.occ 125, .occ 132, .occ 134, .occ 135, .occ 137, .occ 138, .occ 179, .occ 478, .occ 518, .occ 614, .occ 686, .occ 690, .occ 1146, .occ 1166, .occ 1167, .occ 1168, .occ 1187, .occ 1215, .occ 1255, .occ 1256, .occ 1338, .occ 1357, .occ 1396, .occ 1458, .occ 1462, .occ 1470, .occ 1477, .occ 1479, .occ 1495, .occ 1606, .occ 1619, .sumGe, .nonneg 21, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchLe 35 (0), .branchLe 3 (0), .branchGe 24 (1), .branchGe 40 (1), .branchLe 5 (0), .branchGe 41 (1), .branchGe 9 (1)]

def plane484GenLeaf0366Mult : Fin 44 → Nat := ![5417, 1072, 624, 5394, 687, 2449, 1304, 208, 2300, 4899, 5552, 4935, 1046, 1503, 1528, 176, 1453, 5099, 463, 583, 4879, 769, 1639, 444, 2080, 952, 457, 577, 1635, 3753, 2736, 11537, 958, 958, 11443, 8730, 17110, 7015, 6120, 23519, 17689, 6120, 8820, 26539]

theorem plane484GenLeaf0366 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0366Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0366Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0366Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0366Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 179
  · exact hroot.hOcc 478
  · exact hroot.hOcc 518
  · exact hroot.hOcc 614
  · exact hroot.hOcc 686
  · exact hroot.hOcc 690
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1167
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1255
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1338
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1396
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1479
  · exact hroot.hOcc 1495
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1619
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
