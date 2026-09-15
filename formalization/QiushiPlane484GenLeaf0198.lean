import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0198Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 127, .occ 130, .occ 144, .occ 248, .occ 261, .occ 267, .occ 323, .occ 707, .occ 1124, .occ 1140, .occ 1164, .occ 1170, .occ 1179, .occ 1205, .occ 1213, .occ 1214, .occ 1215, .occ 1241, .occ 1341, .occ 1367, .occ 1445, .occ 1458, .occ 1467, .occ 1524, .occ 1538, .occ 1542, .occ 1601, .occ 1606, .occ 1607, .occ 1619, .occ 1620, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchGe 1 (1), .branchLe 22 (0), .branchLe 21 (0), .branchLe 6 (0), .branchGe 38 (1)]

def plane484GenLeaf0198Mult : Fin 44 → Nat := ![5690, 2141, 8942, 8330, 14020, 14020, 3499, 1926, 3772, 6784, 37025, 19311, 2951, 26940, 4770, 762, 20406, 7343, 1821, 8125, 8201, 18584, 1868, 17424, 3717, 4832, 15572, 3670, 16043, 6392, 7258, 3843, 72182, 40909, 72182, 149594, 69386, 64924, 45983, 67301, 35157, 72182, 64351, 110436]

theorem plane484GenLeaf0198 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0198Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0198Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0198Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0198Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 144
  · exact hroot.hOcc 248
  · exact hroot.hOcc 261
  · exact hroot.hOcc 267
  · exact hroot.hOcc 323
  · exact hroot.hOcc 707
  · exact hroot.hOcc 1124
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1241
  · exact hroot.hOcc 1341
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1445
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1538
  · exact hroot.hOcc 1542
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1620
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
