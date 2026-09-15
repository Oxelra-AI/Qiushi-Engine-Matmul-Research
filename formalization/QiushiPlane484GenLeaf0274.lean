import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0274Refs : Fin 44 → RowRef 1665 43 := ![.occ 85, .occ 124, .occ 135, .occ 139, .occ 224, .occ 489, .occ 663, .occ 856, .occ 1102, .occ 1136, .occ 1140, .occ 1143, .occ 1149, .occ 1150, .occ 1154, .occ 1180, .occ 1190, .occ 1196, .occ 1220, .occ 1241, .occ 1425, .occ 1471, .occ 1491, .occ 1602, .occ 1603, .occ 1610, .occ 1632, .occ 1653, .sumGe, .nonneg 3, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchLe 13 (0), .branchGe 37 (1), .branchLe 32 (0), .branchLe 8 (0), .branchLe 9 (0), .branchGe 30 (1), .branchLe 5 (0)]

def plane484GenLeaf0274Mult : Fin 44 → Nat := ![299, 193, 1299, 1926, 1895, 4960, 870, 209, 2989, 2157, 426, 1770, 178, 1569, 1248, 351, 641, 276, 2949, 71, 2519, 501, 1147, 639, 2364, 264, 939, 1287, 8373, 2113, 7003, 293, 2689, 7086, 5508, 7804, 3807, 6900, 12817, 6378, 7801, 6147, 15273, 4472]

theorem plane484GenLeaf0274 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0274Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0274Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0274Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0274Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 124
  · exact hroot.hOcc 135
  · exact hroot.hOcc 139
  · exact hroot.hOcc 224
  · exact hroot.hOcc 489
  · exact hroot.hOcc 663
  · exact hroot.hOcc 856
  · exact hroot.hOcc 1102
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1149
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1180
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1241
  · exact hroot.hOcc 1425
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1632
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5

end QiushiMatmul
