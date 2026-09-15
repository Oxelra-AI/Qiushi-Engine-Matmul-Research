import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0263Refs : Fin 44 → RowRef 1665 43 := ![.occ 107, .occ 110, .occ 125, .occ 132, .occ 136, .occ 141, .occ 385, .occ 694, .occ 750, .occ 860, .occ 1101, .occ 1102, .occ 1140, .occ 1151, .occ 1154, .occ 1183, .occ 1186, .occ 1187, .occ 1248, .occ 1315, .occ 1358, .occ 1471, .occ 1488, .occ 1489, .occ 1491, .occ 1511, .occ 1567, .occ 1609, .occ 1638, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchLe 13 (0), .branchLe 37 (0), .branchLe 10 (0), .branchLe 25 (0), .branchLe 35 (0), .branchLe 33 (0), .branchLe 12 (0)]

def plane484GenLeaf0263Mult : Fin 44 → Nat := ![6204, 8632, 18428, 12455, 1482, 8337, 4527, 13296, 4370, 7427, 3132, 480, 7384, 14152, 484, 2676, 24, 4420, 112, 734, 984, 3754, 3016, 3922, 14366, 7614, 7154, 4248, 7184, 40860, 39876, 22292, 26958, 13364, 27996, 25892, 33922, 36994, 24822, 33950, 2064, 30660, 29262, 40860]

theorem plane484GenLeaf0263 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0263Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0263Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0263Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0263Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 107
  · exact hroot.hOcc 110
  · exact hroot.hOcc 125
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 141
  · exact hroot.hOcc 385
  · exact hroot.hOcc 694
  · exact hroot.hOcc 750
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1102
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1248
  · exact hroot.hOcc 1315
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1511
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1638
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
