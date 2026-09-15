import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0174Refs : Fin 41 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 129, .occ 139, .occ 141, .occ 143, .occ 168, .occ 259, .occ 507, .occ 562, .occ 638, .occ 817, .occ 860, .occ 969, .occ 1025, .occ 1174, .occ 1183, .occ 1240, .occ 1258, .occ 1325, .occ 1471, .occ 1501, .occ 1507, .occ 1529, .occ 1542, .occ 1551, .occ 1557, .occ 1558, .occ 1625, .occ 1653, .occ 1656, .sumGe, .nonneg 1, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchGe 18 (1), .branchLe 42 (0), .branchLe 24 (0)]

def plane484GenLeaf0174Mult : Fin 41 → Nat := ![1565, 1267, 293, 419, 3114, 1842, 1944, 250, 656, 1924, 2538, 1508, 226, 1069, 48, 2271, 246, 2045, 246, 112, 472, 246, 1145, 2021, 52, 194, 48, 52, 24, 1334, 28, 4996, 1021, 4996, 2908, 7154, 4996, 13290, 14712, 4524, 2416]

theorem plane484GenLeaf0174 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0174Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0174Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0174Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0174Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 129
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 168
  · exact hroot.hOcc 259
  · exact hroot.hOcc 507
  · exact hroot.hOcc 562
  · exact hroot.hOcc 638
  · exact hroot.hOcc 817
  · exact hroot.hOcc 860
  · exact hroot.hOcc 969
  · exact hroot.hOcc 1025
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1240
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1501
  · exact hroot.hOcc 1507
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1542
  · exact hroot.hOcc 1551
  · exact hroot.hOcc 1557
  · exact hroot.hOcc 1558
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1653
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24

end QiushiMatmul
