import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0238Refs : Fin 44 → RowRef 1665 43 := ![.occ 90, .occ 123, .occ 128, .occ 144, .occ 252, .occ 714, .occ 1143, .occ 1154, .occ 1170, .occ 1173, .occ 1183, .occ 1187, .occ 1188, .occ 1202, .occ 1213, .occ 1231, .occ 1346, .occ 1351, .occ 1353, .occ 1357, .occ 1429, .occ 1458, .occ 1459, .occ 1491, .occ 1597, .occ 1602, .occ 1603, .occ 1624, .occ 1644, .occ 1647, .sumGe, .branchLe 15 (0), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchLe 16 (0), .branchGe 31 (1), .branchLe 20 (0), .branchGe 30 (1), .branchLe 6 (0), .branchLe 4 (0), .branchLe 18 (0)]

def plane484GenLeaf0238Mult : Fin 44 → Nat := ![1924, 932, 12630, 58, 1362, 8328, 2360, 3582, 4331, 6110, 7000, 8112, 20, 1592, 183, 46, 210, 6734, 988, 7760, 1612, 4622, 4809, 128, 3080, 6545, 2920, 310, 5368, 1528, 28964, 28944, 19858, 11280, 28964, 21346, 21758, 22022, 20452, 7506, 33092, 20698, 26604, 20078]

theorem plane484GenLeaf0238 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0238Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0238Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0238Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0238Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 144
  · exact hroot.hOcc 252
  · exact hroot.hOcc 714
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1202
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1231
  · exact hroot.hOcc 1346
  · exact hroot.hOcc 1351
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1647
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18

end QiushiMatmul
