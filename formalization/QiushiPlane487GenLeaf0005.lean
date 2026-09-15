import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0005Refs : Fin 49 → RowRef 668 48 := ![.occ 82, .occ 83, .occ 102, .occ 103, .occ 125, .occ 126, .occ 152, .occ 156, .occ 203, .occ 222, .occ 223, .occ 231, .occ 240, .occ 257, .occ 258, .occ 269, .occ 275, .occ 303, .occ 315, .occ 346, .occ 347, .occ 350, .occ 380, .occ 386, .occ 388, .occ 391, .occ 399, .occ 471, .occ 516, .occ 560, .occ 563, .occ 577, .occ 582, .occ 586, .occ 597, .occ 608, .occ 609, .occ 638, .occ 639, .sumGe, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchLe 25 (0), .branchLe 12 (0), .branchLe 15 (0), .branchGe 16 (1), .branchLe 14 (0), .branchLe 33 (0)]

def plane487GenLeaf0005Mult : Fin 49 → Nat := ![1588, 8402, 14617, 213, 12885, 16268, 18057, 2395, 24154, 13651, 12477, 11010, 1614, 13785, 10427, 3401, 790, 234, 7165, 6253, 4691, 20876, 5617, 514, 17587, 134, 19647, 6457, 2531, 3590, 244, 4570, 1647, 9452, 332, 354, 8623, 1429, 9091, 43355, 43111, 35400, 36322, 23708, 34264, 19643, 166856, 17714, 19017]

theorem plane487GenLeaf0005 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0005Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0005Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 152
  · exact hroot.hOcc 156
  · exact hroot.hOcc 203
  · exact hroot.hOcc 222
  · exact hroot.hOcc 223
  · exact hroot.hOcc 231
  · exact hroot.hOcc 240
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 269
  · exact hroot.hOcc 275
  · exact hroot.hOcc 303
  · exact hroot.hOcc 315
  · exact hroot.hOcc 346
  · exact hroot.hOcc 347
  · exact hroot.hOcc 350
  · exact hroot.hOcc 380
  · exact hroot.hOcc 386
  · exact hroot.hOcc 388
  · exact hroot.hOcc 391
  · exact hroot.hOcc 399
  · exact hroot.hOcc 471
  · exact hroot.hOcc 516
  · exact hroot.hOcc 560
  · exact hroot.hOcc 563
  · exact hroot.hOcc 577
  · exact hroot.hOcc 582
  · exact hroot.hOcc 586
  · exact hroot.hOcc 597
  · exact hroot.hOcc 608
  · exact hroot.hOcc 609
  · exact hroot.hOcc 638
  · exact hroot.hOcc 639
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (12 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (15 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (16 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (14 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (33 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33

end QiushiMatmul
