import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0509Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 121, .occ 125, .occ 126, .occ 128, .occ 129, .occ 131, .occ 135, .occ 138, .occ 140, .occ 329, .occ 885, .occ 915, .occ 1026, .occ 1116, .occ 1159, .occ 1233, .occ 1265, .occ 1280, .occ 1334, .occ 1342, .occ 1344, .occ 1388, .occ 1472, .occ 1484, .occ 1546, .occ 1615, .occ 1637, .occ 1663, .sumGe, .nonneg 0, .nonneg 9, .nonneg 26, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 30 (0), .branchLe 34 (0), .branchLe 8 (0), .branchLe 33 (0), .branchGe 5 (1), .branchLe 10 (0), .branchLe 41 (0)]

def plane484GenLeaf0509Mult : Fin 43 → Nat := ![1597, 1072, 1190, 69, 429, 1764, 1267, 1581, 798, 2591, 1254, 514, 1568, 86, 231, 1834, 1080, 390, 99, 359, 388, 1414, 335, 607, 1703, 1455, 2517, 612, 179, 5953, 3436, 12, 901, 12034, 4875, 2629, 5953, 3731, 970, 5346, 8078, 2448, 5953]

theorem plane484GenLeaf0509 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0509Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0509Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0509Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0509Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 329
  · exact hroot.hOcc 885
  · exact hroot.hOcc 915
  · exact hroot.hOcc 1026
  · exact hroot.hOcc 1116
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1265
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1344
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1637
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41

end QiushiMatmul
