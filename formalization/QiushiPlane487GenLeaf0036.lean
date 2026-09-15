import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0036Refs : Fin 49 → RowRef 668 48 := ![.occ 89, .occ 92, .occ 93, .occ 106, .occ 118, .occ 119, .occ 191, .occ 218, .occ 219, .occ 226, .occ 231, .occ 263, .occ 294, .occ 296, .occ 303, .occ 306, .occ 312, .occ 322, .occ 367, .occ 386, .occ 391, .occ 396, .occ 428, .occ 442, .occ 444, .occ 465, .occ 469, .occ 471, .occ 472, .occ 474, .occ 476, .occ 478, .occ 530, .occ 604, .occ 608, .occ 624, .occ 633, .occ 650, .sumGe, .nonneg 0, .nonneg 8, .nonneg 14, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchGe 33 (1), .branchGe 12 (1), .branchLe 19 (0), .branchGe 17 (1)]

def plane487GenLeaf0036Mult : Fin 49 → Nat := ![786, 2687, 18509, 3143, 5914, 11349, 8990, 10959, 9411, 4401, 1105, 4903, 251, 12776, 6000, 2235, 7842, 2041, 1951, 14151, 4541, 4597, 432, 2891, 8988, 12063, 796, 4150, 1684, 603, 3715, 1970, 8552, 893, 2250, 643, 3326, 824, 25985, 4403, 8270, 9733, 23477, 22270, 35923, 36025, 45592, 25985, 70776]

theorem plane487GenLeaf0036 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0036Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0036Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0036Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0036Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 92
  · exact hroot.hOcc 93
  · exact hroot.hOcc 106
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 191
  · exact hroot.hOcc 218
  · exact hroot.hOcc 219
  · exact hroot.hOcc 226
  · exact hroot.hOcc 231
  · exact hroot.hOcc 263
  · exact hroot.hOcc 294
  · exact hroot.hOcc 296
  · exact hroot.hOcc 303
  · exact hroot.hOcc 306
  · exact hroot.hOcc 312
  · exact hroot.hOcc 322
  · exact hroot.hOcc 367
  · exact hroot.hOcc 386
  · exact hroot.hOcc 391
  · exact hroot.hOcc 396
  · exact hroot.hOcc 428
  · exact hroot.hOcc 442
  · exact hroot.hOcc 444
  · exact hroot.hOcc 465
  · exact hroot.hOcc 469
  · exact hroot.hOcc 471
  · exact hroot.hOcc 472
  · exact hroot.hOcc 474
  · exact hroot.hOcc 476
  · exact hroot.hOcc 478
  · exact hroot.hOcc 530
  · exact hroot.hOcc 604
  · exact hroot.hOcc 608
  · exact hroot.hOcc 624
  · exact hroot.hOcc 633
  · exact hroot.hOcc 650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (14 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (12 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (17 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
