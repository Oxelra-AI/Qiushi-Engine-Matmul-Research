import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0046Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 131, .occ 133, .occ 141, .occ 150, .occ 165, .occ 166, .occ 581, .occ 614, .occ 615, .occ 1150, .occ 1158, .occ 1174, .occ 1178, .occ 1190, .occ 1205, .occ 1206, .occ 1245, .occ 1284, .occ 1338, .occ 1342, .occ 1382, .occ 1395, .occ 1467, .occ 1477, .occ 1481, .occ 1512, .occ 1525, .occ 1580, .occ 1638, .occ 1659, .sumGe, .nonneg 15, .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchGe 17 (1), .branchLe 7 (0), .branchLe 18 (0), .branchGe 1 (1), .branchLe 38 (0), .branchLe 3 (0)]

def plane484GenLeaf0046Mult : Fin 43 → Nat := ![105316, 13010, 129157, 47909, 33794, 36826, 14138, 108475, 4260, 58735, 3446, 21808, 16896, 7906, 72906, 23886, 99698, 13104, 17878, 22954, 14608, 63988, 11290, 52198, 22960, 58218, 7332, 2934, 26406, 38124, 9564, 256342, 209360, 82834, 145926, 178708, 183436, 611456, 179916, 132802, 234686, 256342, 256342]

theorem plane484GenLeaf0046 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0046Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0046Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0046Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0046Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 141
  · exact hroot.hOcc 150
  · exact hroot.hOcc 165
  · exact hroot.hOcc 166
  · exact hroot.hOcc 581
  · exact hroot.hOcc 614
  · exact hroot.hOcc 615
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1178
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1245
  · exact hroot.hOcc 1284
  · exact hroot.hOcc 1338
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1395
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1512
  · exact hroot.hOcc 1525
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3

end QiushiMatmul
