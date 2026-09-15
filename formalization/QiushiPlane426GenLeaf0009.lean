import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0009Refs : Fin 59 → RowRef 340 58 := ![.occ 29, .occ 44, .occ 71, .occ 74, .occ 79, .occ 86, .occ 88, .occ 98, .occ 99, .occ 100, .occ 104, .occ 116, .occ 117, .occ 121, .occ 122, .occ 123, .occ 124, .occ 126, .occ 138, .occ 140, .occ 141, .occ 142, .occ 144, .occ 164, .occ 205, .occ 208, .occ 230, .occ 234, .occ 235, .occ 242, .occ 249, .occ 280, .occ 281, .occ 311, .occ 312, .occ 313, .occ 329, .occ 336, .sumGe, .nonneg 6, .nonneg 8, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 23, .nonneg 24, .nonneg 28, .nonneg 30, .nonneg 32, .nonneg 38, .nonneg 39, .branchLe 43 (0), .branchLe 14 (0), .branchGe 1 (1), .branchLe 35 (0), .branchLe 4 (0), .branchGe 10 (1), .branchGe 20 (1), .branchLe 57 (0)]

def plane426GenLeaf0009Mult : Fin 59 → Nat := ![1522, 800, 2437, 1214, 2506, 3940, 2469, 36, 4049, 345, 1911, 2673, 1152, 866, 638, 948, 1231, 978, 314, 1170, 125, 589, 3602, 3605, 2394, 199, 420, 249, 299, 1401, 1271, 388, 1144, 1636, 974, 72, 566, 877, 6873, 3117, 2539, 9830, 8389, 2256, 1466, 1505, 4144, 499, 115, 150, 181, 4162, 5721, 10807, 5642, 6873, 827, 9952, 5341]

theorem plane426GenLeaf0009 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_57 : x 57 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0009Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0009Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 29
  · exact hroot.hOcc 44
  · exact hroot.hOcc 71
  · exact hroot.hOcc 74
  · exact hroot.hOcc 79
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 164
  · exact hroot.hOcc 205
  · exact hroot.hOcc 208
  · exact hroot.hOcc 230
  · exact hroot.hOcc 234
  · exact hroot.hOcc 235
  · exact hroot.hOcc 242
  · exact hroot.hOcc 249
  · exact hroot.hOcc 280
  · exact hroot.hOcc 281
  · exact hroot.hOcc 311
  · exact hroot.hOcc 312
  · exact hroot.hOcc 313
  · exact hroot.hOcc 329
  · exact hroot.hOcc 336
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (8 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (30 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (32 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (38 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (39 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (35 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (4 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (10 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (20 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (57 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_57

end QiushiMatmul
