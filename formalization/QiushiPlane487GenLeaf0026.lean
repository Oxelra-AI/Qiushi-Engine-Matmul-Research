import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0026Refs : Fin 49 → RowRef 668 48 := ![.occ 95, .occ 100, .occ 101, .occ 145, .occ 170, .occ 189, .occ 194, .occ 217, .occ 224, .occ 227, .occ 233, .occ 240, .occ 246, .occ 247, .occ 275, .occ 280, .occ 294, .occ 295, .occ 316, .occ 331, .occ 385, .occ 386, .occ 387, .occ 391, .occ 399, .occ 402, .occ 415, .occ 446, .occ 449, .occ 542, .occ 563, .occ 573, .occ 600, .occ 609, .occ 644, .occ 648, .occ 650, .occ 651, .occ 661, .sumGe, .nonneg 28, .branchLe 39 (0), .branchLe 23 (0), .branchGe 6 (1), .branchLe 33 (0), .branchLe 14 (0), .branchGe 29 (1), .branchLe 3 (0), .branchLe 12 (0)]

def plane487GenLeaf0026Mult : Fin 49 → Nat := ![20277, 41428, 19438, 148291, 96210, 81210, 19508, 53237, 15469, 79531, 1678, 130288, 35549, 68770, 52677, 39696, 61147, 126992, 15701, 1033, 47295, 45678, 2420, 32017, 82662, 24293, 76262, 7445, 11741, 49305, 14834, 8414, 84462, 30722, 21171, 32578, 7613, 11946, 70074, 286502, 2206, 172810, 161012, 539921, 203840, 202040, 613444, 263420, 234365]

theorem plane487GenLeaf0026 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0026Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0026Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0026Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0026Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 145
  · exact hroot.hOcc 170
  · exact hroot.hOcc 189
  · exact hroot.hOcc 194
  · exact hroot.hOcc 217
  · exact hroot.hOcc 224
  · exact hroot.hOcc 227
  · exact hroot.hOcc 233
  · exact hroot.hOcc 240
  · exact hroot.hOcc 246
  · exact hroot.hOcc 247
  · exact hroot.hOcc 275
  · exact hroot.hOcc 280
  · exact hroot.hOcc 294
  · exact hroot.hOcc 295
  · exact hroot.hOcc 316
  · exact hroot.hOcc 331
  · exact hroot.hOcc 385
  · exact hroot.hOcc 386
  · exact hroot.hOcc 387
  · exact hroot.hOcc 391
  · exact hroot.hOcc 399
  · exact hroot.hOcc 402
  · exact hroot.hOcc 415
  · exact hroot.hOcc 446
  · exact hroot.hOcc 449
  · exact hroot.hOcc 542
  · exact hroot.hOcc 563
  · exact hroot.hOcc 573
  · exact hroot.hOcc 600
  · exact hroot.hOcc 609
  · exact hroot.hOcc 644
  · exact hroot.hOcc 648
  · exact hroot.hOcc 650
  · exact hroot.hOcc 651
  · exact hroot.hOcc 661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (28 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (33 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (14 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (29 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (3 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
