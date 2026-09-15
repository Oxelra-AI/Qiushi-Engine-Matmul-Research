import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0052Refs : Fin 38 → RowRef 1665 43 := ![.occ 119, .occ 132, .occ 136, .occ 179, .occ 440, .occ 486, .occ 598, .occ 634, .occ 843, .occ 932, .occ 1013, .occ 1174, .occ 1208, .occ 1246, .occ 1296, .occ 1301, .occ 1326, .occ 1405, .occ 1406, .occ 1428, .occ 1467, .occ 1509, .occ 1510, .occ 1562, .occ 1618, .occ 1627, .occ 1634, .occ 1663, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 13 (0), .branchGe 17 (1), .branchGe 7 (1), .branchLe 10 (0), .branchLe 26 (0), .branchLe 5 (0)]

def plane484GenLeaf0052Mult : Fin 38 → Nat := ![540, 296, 466, 42, 38, 118, 376, 182, 452, 222, 246, 289, 251, 148, 106, 38, 160, 221, 22, 55, 414, 185, 168, 55, 24, 98, 50, 234, 1094, 582, 578, 414, 996, 2828, 3226, 1044, 414, 996]

theorem plane484GenLeaf0052 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0052Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0052Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0052Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0052Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 179
  · exact hroot.hOcc 440
  · exact hroot.hOcc 486
  · exact hroot.hOcc 598
  · exact hroot.hOcc 634
  · exact hroot.hOcc 843
  · exact hroot.hOcc 932
  · exact hroot.hOcc 1013
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1246
  · exact hroot.hOcc 1296
  · exact hroot.hOcc 1301
  · exact hroot.hOcc 1326
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1406
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1509
  · exact hroot.hOcc 1510
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1627
  · exact hroot.hOcc 1634
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5

end QiushiMatmul
