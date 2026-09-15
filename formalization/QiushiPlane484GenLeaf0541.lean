import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0541Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 130, .occ 131, .occ 138, .occ 180, .occ 224, .occ 284, .occ 295, .occ 581, .occ 594, .occ 713, .occ 1081, .occ 1116, .occ 1158, .occ 1159, .occ 1160, .occ 1170, .occ 1188, .occ 1317, .occ 1349, .occ 1402, .occ 1440, .occ 1483, .occ 1484, .occ 1492, .occ 1563, .occ 1603, .occ 1606, .occ 1610, .occ 1615, .occ 1624, .occ 1646, .sumGe, .nonneg 18, .nonneg 19, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchLe 1 (0), .branchGe 0 (1), .branchLe 21 (0), .branchLe 7 (0)]

def plane484GenLeaf0541Mult : Fin 44 → Nat := ![3555, 5467, 5375, 8271, 5903, 9209, 9368, 4747, 1397, 15687, 686, 3814, 211, 7146, 11840, 8056, 19547, 4814, 4644, 40, 77, 1121, 4697, 2175, 2232, 328, 1134, 11827, 412, 7365, 6174, 79, 31726, 2952, 1546, 36204, 82997, 29494, 16676, 64119, 30329, 52828, 24418, 25552]

theorem plane484GenLeaf0541 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0541Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0541Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0541Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0541Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 138
  · exact hroot.hOcc 180
  · exact hroot.hOcc 224
  · exact hroot.hOcc 284
  · exact hroot.hOcc 295
  · exact hroot.hOcc 581
  · exact hroot.hOcc 594
  · exact hroot.hOcc 713
  · exact hroot.hOcc 1081
  · exact hroot.hOcc 1116
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1317
  · exact hroot.hOcc 1349
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1563
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1646
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7

end QiushiMatmul
