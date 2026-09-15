import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0018Refs : Fin 49 → RowRef 668 48 := ![.occ 102, .occ 103, .occ 106, .occ 108, .occ 168, .occ 216, .occ 223, .occ 225, .occ 229, .occ 238, .occ 246, .occ 257, .occ 291, .occ 295, .occ 303, .occ 313, .occ 315, .occ 318, .occ 340, .occ 342, .occ 377, .occ 385, .occ 389, .occ 399, .occ 402, .occ 453, .occ 493, .occ 497, .occ 498, .occ 499, .occ 521, .occ 566, .occ 573, .occ 576, .occ 595, .occ 618, .occ 623, .occ 648, .occ 664, .occ 666, .sumGe, .nonneg 7, .nonneg 33, .branchLe 39 (0), .branchLe 23 (0), .branchLe 6 (0), .branchGe 25 (1), .branchGe 1 (1), .branchLe 35 (0)]

def plane487GenLeaf0018Mult : Fin 49 → Nat := ![58456, 434610, 29678, 225350, 134303, 161335, 229964, 77100, 670291, 678740, 54515, 31584, 137223, 6062, 147732, 152, 128936, 156338, 213442, 606746, 149805, 51720, 32588, 377835, 114704, 178629, 46151, 60477, 49905, 109030, 134390, 12582, 270415, 295135, 212165, 326865, 36038, 1912, 25968, 107876, 1014071, 356787, 94136, 726033, 695070, 1006097, 3799334, 2564351, 980575]

theorem plane487GenLeaf0018 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0018Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0018Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0018Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0018Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 168
  · exact hroot.hOcc 216
  · exact hroot.hOcc 223
  · exact hroot.hOcc 225
  · exact hroot.hOcc 229
  · exact hroot.hOcc 238
  · exact hroot.hOcc 246
  · exact hroot.hOcc 257
  · exact hroot.hOcc 291
  · exact hroot.hOcc 295
  · exact hroot.hOcc 303
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 318
  · exact hroot.hOcc 340
  · exact hroot.hOcc 342
  · exact hroot.hOcc 377
  · exact hroot.hOcc 385
  · exact hroot.hOcc 389
  · exact hroot.hOcc 399
  · exact hroot.hOcc 402
  · exact hroot.hOcc 453
  · exact hroot.hOcc 493
  · exact hroot.hOcc 497
  · exact hroot.hOcc 498
  · exact hroot.hOcc 499
  · exact hroot.hOcc 521
  · exact hroot.hOcc 566
  · exact hroot.hOcc 573
  · exact hroot.hOcc 576
  · exact hroot.hOcc 595
  · exact hroot.hOcc 618
  · exact hroot.hOcc 623
  · exact hroot.hOcc 648
  · exact hroot.hOcc 664
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (33 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (39 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (6 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (25 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (1 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (35 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35

end QiushiMatmul
