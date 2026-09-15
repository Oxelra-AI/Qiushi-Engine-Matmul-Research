import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0051Refs : Fin 50 → RowRef 726 49 := ![.occ 100, .occ 106, .occ 107, .occ 111, .occ 113, .occ 186, .occ 188, .occ 189, .occ 230, .occ 257, .occ 293, .occ 299, .occ 324, .occ 355, .occ 365, .occ 367, .occ 372, .occ 394, .occ 410, .occ 422, .occ 439, .occ 461, .occ 511, .occ 523, .occ 539, .occ 569, .occ 570, .occ 571, .occ 573, .occ 626, .occ 632, .occ 642, .occ 647, .occ 653, .occ 661, .occ 662, .occ 714, .occ 715, .occ 720, .sumGe, .nonneg 24, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchLe 11 (0), .branchLe 23 (0), .branchLe 0 (0), .branchLe 43 (0), .branchGe 6 (1), .branchGe 42 (1)]

def plane491GenLeaf0051Mult : Fin 50 → Nat := ![225274, 247474, 192485, 134953, 12219, 99388, 14643, 51141, 50850, 10578, 30847, 135724, 43410, 64962, 21904, 10096, 32408, 22983, 76960, 96764, 65825, 6072, 65984, 27588, 46958, 22006, 15291, 18187, 68, 34546, 50258, 39362, 3652, 125274, 34892, 16220, 12346, 31052, 35778, 281724, 56331, 200542, 221057, 912241, 83778, 165402, 245946, 57568, 148510, 1024295]

theorem plane491GenLeaf0051 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0051Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0051Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0051Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0051Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 100
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 111
  · exact hroot.hOcc 113
  · exact hroot.hOcc 186
  · exact hroot.hOcc 188
  · exact hroot.hOcc 189
  · exact hroot.hOcc 230
  · exact hroot.hOcc 257
  · exact hroot.hOcc 293
  · exact hroot.hOcc 299
  · exact hroot.hOcc 324
  · exact hroot.hOcc 355
  · exact hroot.hOcc 365
  · exact hroot.hOcc 367
  · exact hroot.hOcc 372
  · exact hroot.hOcc 394
  · exact hroot.hOcc 410
  · exact hroot.hOcc 422
  · exact hroot.hOcc 439
  · exact hroot.hOcc 461
  · exact hroot.hOcc 511
  · exact hroot.hOcc 523
  · exact hroot.hOcc 539
  · exact hroot.hOcc 569
  · exact hroot.hOcc 570
  · exact hroot.hOcc 571
  · exact hroot.hOcc 573
  · exact hroot.hOcc 626
  · exact hroot.hOcc 632
  · exact hroot.hOcc 642
  · exact hroot.hOcc 647
  · exact hroot.hOcc 653
  · exact hroot.hOcc 661
  · exact hroot.hOcc 662
  · exact hroot.hOcc 714
  · exact hroot.hOcc 715
  · exact hroot.hOcc 720
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (24 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (42 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
