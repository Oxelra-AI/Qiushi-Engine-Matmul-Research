import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0481Refs : Fin 43 → RowRef 1665 43 := ![.occ 86, .occ 120, .occ 131, .occ 133, .occ 140, .occ 142, .occ 170, .occ 268, .occ 675, .occ 1109, .occ 1111, .occ 1145, .occ 1159, .occ 1168, .occ 1172, .occ 1188, .occ 1200, .occ 1205, .occ 1216, .occ 1276, .occ 1311, .occ 1350, .occ 1454, .occ 1470, .occ 1477, .occ 1484, .occ 1489, .occ 1596, .occ 1609, .occ 1629, .occ 1651, .sumGe, .nonneg 18, .nonneg 25, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 3 (0), .branchGe 38 (1), .branchGe 34 (1), .branchLe 28 (0), .branchGe 32 (1)]

def plane484GenLeaf0481Mult : Fin 43 → Nat := ![86, 398, 1017, 621, 265, 369, 846, 712, 354, 168, 246, 109, 274, 98, 360, 156, 334, 210, 370, 140, 374, 287, 225, 48, 108, 854, 1, 48, 402, 70, 92, 1708, 86, 216, 4828, 370, 1462, 1580, 1264, 2400, 808, 1708, 3876]

theorem plane484GenLeaf0481 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0481Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0481Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0481Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0481Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 120
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 170
  · exact hroot.hOcc 268
  · exact hroot.hOcc 675
  · exact hroot.hOcc 1109
  · exact hroot.hOcc 1111
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1276
  · exact hroot.hOcc 1311
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1454
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1596
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1651
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32

end QiushiMatmul
