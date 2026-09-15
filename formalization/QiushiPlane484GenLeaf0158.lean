import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0158Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 132, .occ 137, .occ 139, .occ 358, .occ 402, .occ 440, .occ 508, .occ 767, .occ 932, .occ 1166, .occ 1183, .occ 1186, .occ 1238, .occ 1248, .occ 1290, .occ 1296, .occ 1321, .occ 1353, .occ 1355, .occ 1373, .occ 1467, .occ 1486, .occ 1489, .occ 1519, .occ 1548, .occ 1571, .occ 1603, .occ 1628, .occ 1636, .sumGe, .nonneg 2, .nonneg 11, .branchLe 15 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchLe 30 (0), .branchGe 21 (1), .branchLe 25 (0), .branchLe 14 (0), .branchLe 6 (0)]

def plane484GenLeaf0158Mult : Fin 44 → Nat := ![24330, 26498, 19960, 2062, 24090, 462, 44502, 3086, 12072, 1500, 1908, 5578, 28766, 11074, 3170, 1200, 10533, 1565, 1084, 4617, 3873, 2824, 1324, 7832, 9348, 1084, 3170, 7832, 7578, 14024, 21506, 65936, 22484, 23928, 64612, 59544, 50272, 103422, 6662, 37170, 149540, 62766, 65936, 65936]

theorem plane484GenLeaf0158 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0158Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0158Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0158Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0158Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 358
  · exact hroot.hOcc 402
  · exact hroot.hOcc 440
  · exact hroot.hOcc 508
  · exact hroot.hOcc 767
  · exact hroot.hOcc 932
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1248
  · exact hroot.hOcc 1290
  · exact hroot.hOcc 1296
  · exact hroot.hOcc 1321
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1355
  · exact hroot.hOcc 1373
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1519
  · exact hroot.hOcc 1548
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1636
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6

end QiushiMatmul
