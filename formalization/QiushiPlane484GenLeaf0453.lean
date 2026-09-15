import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0453Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 133, .occ 135, .occ 138, .occ 155, .occ 156, .occ 191, .occ 283, .occ 396, .occ 412, .occ 419, .occ 462, .occ 610, .occ 961, .occ 1151, .occ 1179, .occ 1200, .occ 1206, .occ 1232, .occ 1241, .occ 1250, .occ 1276, .occ 1283, .occ 1317, .occ 1318, .occ 1337, .occ 1453, .occ 1471, .occ 1543, .occ 1567, .occ 1590, .occ 1619, .occ 1629, .occ 1646, .occ 1656, .sumGe, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchGe 29 (1), .branchLe 27 (0), .branchLe 42 (0), .branchGe 40 (1)]

def plane484GenLeaf0453Mult : Fin 44 → Nat := ![416, 2254, 2388, 810, 2636, 120, 394, 596, 4660, 2516, 5970, 1306, 1238, 745, 1001, 348, 1826, 405, 854, 791, 2659, 283, 133, 2759, 69, 1374, 2099, 960, 266, 677, 1002, 214, 331, 913, 133, 7030, 22756, 5486, 6028, 6816, 24710, 4202, 3640, 25034]

theorem plane484GenLeaf0453 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0453Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0453Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0453Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0453Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 155
  · exact hroot.hOcc 156
  · exact hroot.hOcc 191
  · exact hroot.hOcc 283
  · exact hroot.hOcc 396
  · exact hroot.hOcc 412
  · exact hroot.hOcc 419
  · exact hroot.hOcc 462
  · exact hroot.hOcc 610
  · exact hroot.hOcc 961
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1232
  · exact hroot.hOcc 1241
  · exact hroot.hOcc 1250
  · exact hroot.hOcc 1276
  · exact hroot.hOcc 1283
  · exact hroot.hOcc 1317
  · exact hroot.hOcc 1318
  · exact hroot.hOcc 1337
  · exact hroot.hOcc 1453
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1543
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1646
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
