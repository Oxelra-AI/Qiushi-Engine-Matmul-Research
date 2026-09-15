import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0518Refs : Fin 44 → RowRef 1665 43 := ![.occ 126, .occ 131, .occ 133, .occ 199, .occ 250, .occ 290, .occ 573, .occ 664, .occ 815, .occ 869, .occ 1109, .occ 1111, .occ 1145, .occ 1159, .occ 1188, .occ 1206, .occ 1213, .occ 1293, .occ 1324, .occ 1358, .occ 1386, .occ 1447, .occ 1467, .occ 1481, .occ 1486, .occ 1488, .occ 1546, .occ 1590, .occ 1597, .occ 1606, .occ 1660, .occ 1664, .sumGe, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchGe 34 (1), .branchLe 9 (0), .branchLe 18 (0), .branchLe 3 (0), .branchLe 13 (0), .branchLe 22 (0)]

def plane484GenLeaf0518Mult : Fin 44 → Nat := ![46010, 30870, 67506, 11493, 33293, 3532, 19875, 20718, 20112, 1613, 19785, 4861, 24646, 64123, 25902, 78349, 11395, 28426, 22944, 20111, 23671, 39449, 961, 14717, 4007, 35831, 8865, 500, 7326, 11185, 27815, 13262, 170898, 315197, 158224, 15981, 170898, 144996, 308367, 66428, 144996, 84189, 170898, 166891]

theorem plane484GenLeaf0518 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0518Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0518Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0518Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0518Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 126
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 199
  · exact hroot.hOcc 250
  · exact hroot.hOcc 290
  · exact hroot.hOcc 573
  · exact hroot.hOcc 664
  · exact hroot.hOcc 815
  · exact hroot.hOcc 869
  · exact hroot.hOcc 1109
  · exact hroot.hOcc 1111
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1293
  · exact hroot.hOcc 1324
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1386
  · exact hroot.hOcc 1447
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1660
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22

end QiushiMatmul
