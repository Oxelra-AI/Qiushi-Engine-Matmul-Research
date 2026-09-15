import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0547Refs : Fin 43 → RowRef 1665 43 := ![.occ 94, .occ 128, .occ 131, .occ 133, .occ 138, .occ 140, .occ 142, .occ 212, .occ 289, .occ 367, .occ 437, .occ 654, .occ 693, .occ 864, .occ 868, .occ 1081, .occ 1100, .occ 1154, .occ 1158, .occ 1179, .occ 1200, .occ 1206, .occ 1214, .occ 1260, .occ 1453, .occ 1471, .occ 1472, .occ 1483, .occ 1619, .sumGe, .nonneg 3, .nonneg 19, .nonneg 39, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchGe 30 (1), .branchGe 1 (1), .branchLe 11 (0), .branchLe 32 (0), .branchGe 28 (1), .branchLe 9 (0), .branchLe 6 (0)]

def plane484GenLeaf0547Mult : Fin 43 → Nat := ![108, 226, 244, 49, 45, 277, 292, 565, 2, 124, 103, 193, 81, 85, 149, 28, 2, 65, 48, 46, 314, 328, 65, 99, 46, 2, 313, 392, 167, 753, 20, 65, 15, 2109, 1206, 366, 620, 618, 177, 753, 1565, 586, 705]

theorem plane484GenLeaf0547 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0547Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0547Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0547Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0547Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 94
  · exact hroot.hOcc 128
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 212
  · exact hroot.hOcc 289
  · exact hroot.hOcc 367
  · exact hroot.hOcc 437
  · exact hroot.hOcc 654
  · exact hroot.hOcc 693
  · exact hroot.hOcc 864
  · exact hroot.hOcc 868
  · exact hroot.hOcc 1081
  · exact hroot.hOcc 1100
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1453
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1619
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (11 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6

end QiushiMatmul
