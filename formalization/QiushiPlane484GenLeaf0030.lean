import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0030Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 128, .occ 131, .occ 139, .occ 317, .occ 615, .occ 709, .occ 752, .occ 787, .occ 800, .occ 803, .occ 818, .occ 1170, .occ 1173, .occ 1213, .occ 1264, .occ 1266, .occ 1268, .occ 1303, .occ 1334, .occ 1392, .occ 1396, .occ 1399, .occ 1426, .occ 1457, .occ 1458, .occ 1472, .occ 1580, .occ 1606, .occ 1607, .occ 1626, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchLe 25 (0), .branchLe 18 (0), .branchGe 42 (1), .branchGe 23 (1), .branchLe 7 (0)]

def plane484GenLeaf0030Mult : Fin 44 → Nat := ![16507, 8648, 4947, 43910, 31518, 25663, 3837, 34709, 101467, 72882, 17523, 9929, 43910, 5347, 1346, 30795, 25569, 10924, 2676, 34701, 1747, 10126, 8752, 65667, 11212, 4344, 52272, 25054, 45141, 3200, 2071, 146786, 78893, 146786, 146786, 146786, 137095, 119052, 361294, 126684, 22636, 286093, 144266, 143586]

theorem plane484GenLeaf0030 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0030Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0030Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0030Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0030Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 128
  · exact hroot.hOcc 131
  · exact hroot.hOcc 139
  · exact hroot.hOcc 317
  · exact hroot.hOcc 615
  · exact hroot.hOcc 709
  · exact hroot.hOcc 752
  · exact hroot.hOcc 787
  · exact hroot.hOcc 800
  · exact hroot.hOcc 803
  · exact hroot.hOcc 818
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1266
  · exact hroot.hOcc 1268
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1396
  · exact hroot.hOcc 1399
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1457
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1626
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7

end QiushiMatmul
