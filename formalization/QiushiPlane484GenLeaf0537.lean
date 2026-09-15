import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0537Refs : Fin 42 → RowRef 1665 43 := ![.occ 133, .occ 196, .occ 224, .occ 325, .occ 403, .occ 471, .occ 596, .occ 599, .occ 815, .occ 1160, .occ 1205, .occ 1208, .occ 1221, .occ 1227, .occ 1236, .occ 1261, .occ 1267, .occ 1327, .occ 1343, .occ 1348, .occ 1369, .occ 1433, .occ 1446, .occ 1518, .occ 1541, .occ 1571, .occ 1597, .occ 1615, .occ 1637, .sumGe, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchLe 1 (0), .branchLe 0 (0), .branchGe 19 (1), .branchLe 6 (0), .branchLe 20 (0), .branchLe 13 (0), .branchGe 37 (1)]

def plane484GenLeaf0537Mult : Fin 42 → Nat := ![2633, 8646, 4422, 12419, 6494, 2115, 46, 16201, 5634, 1034, 9341, 501, 1611, 1502, 1237, 353, 8716, 159, 334, 1532, 756, 3359, 11850, 3547, 1844, 4135, 1316, 589, 1503, 18057, 36859, 26972, 27, 2291, 47918, 4266, 16434, 31941, 17898, 17723, 16221, 53748]

theorem plane484GenLeaf0537 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0537Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0537Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0537Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0537Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 133
  · exact hroot.hOcc 196
  · exact hroot.hOcc 224
  · exact hroot.hOcc 325
  · exact hroot.hOcc 403
  · exact hroot.hOcc 471
  · exact hroot.hOcc 596
  · exact hroot.hOcc 599
  · exact hroot.hOcc 815
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1221
  · exact hroot.hOcc 1227
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1261
  · exact hroot.hOcc 1267
  · exact hroot.hOcc 1327
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1369
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1446
  · exact hroot.hOcc 1518
  · exact hroot.hOcc 1541
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1637
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
