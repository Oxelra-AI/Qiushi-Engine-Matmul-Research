import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0050Refs : Fin 50 → RowRef 726 49 := ![.occ 78, .occ 100, .occ 106, .occ 117, .occ 120, .occ 150, .occ 151, .occ 161, .occ 177, .occ 219, .occ 221, .occ 230, .occ 231, .occ 244, .occ 255, .occ 296, .occ 299, .occ 305, .occ 315, .occ 347, .occ 363, .occ 424, .occ 486, .occ 490, .occ 511, .occ 573, .occ 580, .occ 586, .occ 590, .occ 622, .occ 631, .occ 632, .occ 634, .occ 642, .occ 645, .occ 647, .occ 707, .occ 713, .occ 720, .sumGe, .nonneg 33, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchLe 11 (0), .branchLe 23 (0), .branchLe 0 (0), .branchLe 43 (0), .branchGe 6 (1), .branchLe 42 (0)]

def plane491GenLeaf0050Mult : Fin 50 → Nat := ![1278, 50903, 47384, 4034, 4393, 5035, 2557, 4958, 4789, 596, 12421, 5755, 1641, 4779, 9459, 5702, 255, 3519, 4778, 743, 1508, 9281, 6835, 6583, 8147, 5801, 3400, 1235, 15962, 3792, 6637, 9285, 10973, 10541, 1752, 14450, 44, 18207, 4415, 52411, 624, 48619, 24221, 137737, 28632, 47952, 28396, 52411, 89693, 44009]

theorem plane491GenLeaf0050 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0050Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0050Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0050Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0050Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 100
  · exact hroot.hOcc 106
  · exact hroot.hOcc 117
  · exact hroot.hOcc 120
  · exact hroot.hOcc 150
  · exact hroot.hOcc 151
  · exact hroot.hOcc 161
  · exact hroot.hOcc 177
  · exact hroot.hOcc 219
  · exact hroot.hOcc 221
  · exact hroot.hOcc 230
  · exact hroot.hOcc 231
  · exact hroot.hOcc 244
  · exact hroot.hOcc 255
  · exact hroot.hOcc 296
  · exact hroot.hOcc 299
  · exact hroot.hOcc 305
  · exact hroot.hOcc 315
  · exact hroot.hOcc 347
  · exact hroot.hOcc 363
  · exact hroot.hOcc 424
  · exact hroot.hOcc 486
  · exact hroot.hOcc 490
  · exact hroot.hOcc 511
  · exact hroot.hOcc 573
  · exact hroot.hOcc 580
  · exact hroot.hOcc 586
  · exact hroot.hOcc 590
  · exact hroot.hOcc 622
  · exact hroot.hOcc 631
  · exact hroot.hOcc 632
  · exact hroot.hOcc 634
  · exact hroot.hOcc 642
  · exact hroot.hOcc 645
  · exact hroot.hOcc 647
  · exact hroot.hOcc 707
  · exact hroot.hOcc 713
  · exact hroot.hOcc 720
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (42 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42

end QiushiMatmul
