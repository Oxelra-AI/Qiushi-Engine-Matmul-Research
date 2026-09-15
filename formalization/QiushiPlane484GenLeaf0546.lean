import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0546Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 122, .occ 123, .occ 125, .occ 128, .occ 129, .occ 131, .occ 138, .occ 140, .occ 142, .occ 286, .occ 679, .occ 787, .occ 858, .occ 1154, .occ 1158, .occ 1160, .occ 1188, .occ 1205, .occ 1222, .occ 1236, .occ 1289, .occ 1303, .occ 1467, .occ 1470, .occ 1471, .occ 1480, .occ 1484, .occ 1590, .occ 1650, .sumGe, .nonneg 10, .nonneg 11, .nonneg 17, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchGe 1 (1), .branchLe 32 (0), .branchLe 28 (0), .branchGe 8 (1)]

def plane484GenLeaf0546Mult : Fin 43 → Nat := ![33, 198, 39, 45, 196, 47, 184, 112, 24, 28, 132, 184, 92, 8, 12, 16, 8, 28, 276, 20, 4, 12, 8, 92, 24, 24, 68, 16, 140, 16, 316, 418, 16, 224, 684, 324, 212, 128, 272, 686, 24, 316, 1030]

theorem plane484GenLeaf0546 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0546Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0546Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0546Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0546Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 286
  · exact hroot.hOcc 679
  · exact hroot.hOcc 787
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1289
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1480
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
