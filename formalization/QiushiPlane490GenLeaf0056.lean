import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0056Refs : Fin 44 → RowRef 713 43 := ![.occ 162, .occ 171, .occ 191, .occ 198, .occ 233, .occ 240, .occ 247, .occ 249, .occ 272, .occ 291, .occ 302, .occ 314, .occ 316, .occ 336, .occ 421, .occ 460, .occ 468, .occ 478, .occ 486, .occ 518, .occ 519, .occ 583, .occ 591, .occ 609, .occ 629, .occ 649, .occ 666, .occ 668, .occ 679, .occ 694, .occ 699, .occ 711, .sumGe, .nonneg 27, .nonneg 38, .nonneg 40, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchGe 30 (1), .branchGe 6 (1), .branchLe 22 (0), .branchGe 39 (1), .branchLe 31 (0)]

def plane490GenLeaf0056Mult : Fin 44 → Nat := ![4047, 9803, 35022, 10604, 19600, 1247, 14338, 16761, 5490, 13533, 17416, 12527, 212, 18455, 2763, 2705, 5019, 244, 14958, 1553, 946, 4025, 2572, 5131, 5266, 8204, 5190, 3796, 7659, 5362, 1481, 1468, 40212, 20511, 5670, 16109, 39968, 25198, 89304, 134875, 11750, 25874, 22839, 37507]

theorem plane490GenLeaf0056 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0056Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0056Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0056Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0056Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 162
  · exact hroot.hOcc 171
  · exact hroot.hOcc 191
  · exact hroot.hOcc 198
  · exact hroot.hOcc 233
  · exact hroot.hOcc 240
  · exact hroot.hOcc 247
  · exact hroot.hOcc 249
  · exact hroot.hOcc 272
  · exact hroot.hOcc 291
  · exact hroot.hOcc 302
  · exact hroot.hOcc 314
  · exact hroot.hOcc 316
  · exact hroot.hOcc 336
  · exact hroot.hOcc 421
  · exact hroot.hOcc 460
  · exact hroot.hOcc 468
  · exact hroot.hOcc 478
  · exact hroot.hOcc 486
  · exact hroot.hOcc 518
  · exact hroot.hOcc 519
  · exact hroot.hOcc 583
  · exact hroot.hOcc 591
  · exact hroot.hOcc 609
  · exact hroot.hOcc 629
  · exact hroot.hOcc 649
  · exact hroot.hOcc 666
  · exact hroot.hOcc 668
  · exact hroot.hOcc 679
  · exact hroot.hOcc 694
  · exact hroot.hOcc 699
  · exact hroot.hOcc 711
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31

end QiushiMatmul
