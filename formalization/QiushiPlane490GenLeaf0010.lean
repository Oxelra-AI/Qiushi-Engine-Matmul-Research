import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0010Refs : Fin 44 → RowRef 713 43 := ![.occ 86, .occ 104, .occ 106, .occ 168, .occ 171, .occ 208, .occ 237, .occ 245, .occ 257, .occ 283, .occ 290, .occ 304, .occ 317, .occ 338, .occ 354, .occ 357, .occ 375, .occ 395, .occ 447, .occ 467, .occ 480, .occ 484, .occ 491, .occ 518, .occ 519, .occ 525, .occ 532, .occ 533, .occ 599, .occ 613, .occ 649, .occ 666, .occ 667, .occ 703, .sumGe, .nonneg 14, .branchLe 29 (0), .branchLe 4 (0), .branchLe 23 (0), .branchLe 16 (0), .branchGe 39 (1), .branchLe 17 (0), .branchLe 22 (0), .branchGe 20 (1)]

def plane490GenLeaf0010Mult : Fin 44 → Nat := ![4793, 9209, 24405, 6277, 19293, 11407, 4077, 3570, 8796, 717, 3317, 2645, 6254, 2086, 8198, 1483, 15182, 2119, 3611, 409, 1576, 4171, 2207, 2170, 3494, 1498, 956, 2818, 8960, 2910, 1550, 8413, 4825, 2695, 27100, 1441, 27100, 19612, 24026, 16568, 62061, 16207, 18863, 72091]

theorem plane490GenLeaf0010 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0010Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0010Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 168
  · exact hroot.hOcc 171
  · exact hroot.hOcc 208
  · exact hroot.hOcc 237
  · exact hroot.hOcc 245
  · exact hroot.hOcc 257
  · exact hroot.hOcc 283
  · exact hroot.hOcc 290
  · exact hroot.hOcc 304
  · exact hroot.hOcc 317
  · exact hroot.hOcc 338
  · exact hroot.hOcc 354
  · exact hroot.hOcc 357
  · exact hroot.hOcc 375
  · exact hroot.hOcc 395
  · exact hroot.hOcc 447
  · exact hroot.hOcc 467
  · exact hroot.hOcc 480
  · exact hroot.hOcc 484
  · exact hroot.hOcc 491
  · exact hroot.hOcc 518
  · exact hroot.hOcc 519
  · exact hroot.hOcc 525
  · exact hroot.hOcc 532
  · exact hroot.hOcc 533
  · exact hroot.hOcc 599
  · exact hroot.hOcc 613
  · exact hroot.hOcc 649
  · exact hroot.hOcc 666
  · exact hroot.hOcc 667
  · exact hroot.hOcc 703
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
