import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0013Refs : Fin 50 → RowRef 726 49 := ![.occ 79, .occ 81, .occ 85, .occ 108, .occ 111, .occ 119, .occ 125, .occ 126, .occ 128, .occ 142, .occ 144, .occ 194, .occ 221, .occ 237, .occ 254, .occ 260, .occ 341, .occ 382, .occ 385, .occ 410, .occ 490, .occ 491, .occ 502, .occ 506, .occ 531, .occ 552, .occ 559, .occ 573, .occ 575, .occ 576, .occ 600, .occ 603, .occ 628, .occ 631, .occ 651, .occ 695, .occ 712, .occ 716, .occ 723, .sumGe, .nonneg 16, .branchLe 31 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchLe 38 (0), .branchGe 6 (1), .branchGe 0 (1), .branchGe 3 (1)]

def plane491GenLeaf0013Mult : Fin 50 → Nat := ![59440, 52402, 52906, 16593, 36589, 22874, 14508, 56591, 14270, 696, 13750, 1236, 15511, 18438, 31006, 15503, 27303, 5438, 5117, 9538, 7126, 11735, 4432, 17300, 10119, 9206, 20376, 16812, 993, 4219, 1275, 15821, 10054, 15, 18191, 2389, 10021, 15999, 4759, 83912, 5613, 53035, 40592, 73858, 62341, 72317, 60965, 64163, 231375, 215772]

theorem plane491GenLeaf0013 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0013Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0013Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 108
  · exact hroot.hOcc 111
  · exact hroot.hOcc 119
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 194
  · exact hroot.hOcc 221
  · exact hroot.hOcc 237
  · exact hroot.hOcc 254
  · exact hroot.hOcc 260
  · exact hroot.hOcc 341
  · exact hroot.hOcc 382
  · exact hroot.hOcc 385
  · exact hroot.hOcc 410
  · exact hroot.hOcc 490
  · exact hroot.hOcc 491
  · exact hroot.hOcc 502
  · exact hroot.hOcc 506
  · exact hroot.hOcc 531
  · exact hroot.hOcc 552
  · exact hroot.hOcc 559
  · exact hroot.hOcc 573
  · exact hroot.hOcc 575
  · exact hroot.hOcc 576
  · exact hroot.hOcc 600
  · exact hroot.hOcc 603
  · exact hroot.hOcc 628
  · exact hroot.hOcc 631
  · exact hroot.hOcc 651
  · exact hroot.hOcc 695
  · exact hroot.hOcc 712
  · exact hroot.hOcc 716
  · exact hroot.hOcc 723
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (0 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (3 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
