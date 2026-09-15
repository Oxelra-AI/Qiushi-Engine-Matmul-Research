import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0248Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 120, .occ 123, .occ 124, .occ 125, .occ 139, .occ 482, .occ 503, .occ 614, .occ 655, .occ 807, .occ 856, .occ 858, .occ 1004, .occ 1170, .occ 1187, .occ 1191, .occ 1196, .occ 1205, .occ 1208, .occ 1244, .occ 1327, .occ 1403, .occ 1472, .occ 1477, .occ 1492, .occ 1540, .occ 1597, .occ 1609, .occ 1617, .occ 1655, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchGe 16 (1), .branchLe 13 (0), .branchGe 41 (1), .branchLe 40 (0), .branchLe 31 (0), .branchLe 14 (0)]

def plane484GenLeaf0248Mult : Fin 44 → Nat := ![5688, 20002, 3545, 1725, 9200, 5058, 6658, 10679, 27801, 4657, 21597, 3853, 14112, 6039, 5992, 599, 1719, 18433, 6360, 19438, 2600, 1765, 37, 3715, 13673, 160, 3888, 3966, 13602, 7500, 574, 52784, 24812, 24510, 52210, 40226, 52624, 3302, 60400, 41907, 51469, 51065, 52185, 43010]

theorem plane484GenLeaf0248 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0248Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0248Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0248Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0248Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 139
  · exact hroot.hOcc 482
  · exact hroot.hOcc 503
  · exact hroot.hOcc 614
  · exact hroot.hOcc 655
  · exact hroot.hOcc 807
  · exact hroot.hOcc 856
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1004
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1244
  · exact hroot.hOcc 1327
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1540
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1617
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
