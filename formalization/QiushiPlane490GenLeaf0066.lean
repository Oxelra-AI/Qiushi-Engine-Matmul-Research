import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0066Refs : Fin 42 → RowRef 713 43 := ![.occ 100, .occ 111, .occ 117, .occ 119, .occ 134, .occ 151, .occ 175, .occ 193, .occ 195, .occ 196, .occ 202, .occ 211, .occ 219, .occ 244, .occ 263, .occ 290, .occ 295, .occ 350, .occ 375, .occ 433, .occ 460, .occ 464, .occ 468, .occ 482, .occ 542, .occ 567, .occ 575, .occ 578, .occ 621, .occ 700, .occ 706, .occ 708, .sumGe, .nonneg 28, .nonneg 41, .branchLe 29 (0), .branchGe 4 (1), .branchLe 34 (0), .branchGe 23 (1), .branchLe 25 (0), .branchLe 18 (0), .branchGe 21 (1)]

def plane490GenLeaf0066Mult : Fin 42 → Nat := ![505, 731, 80, 1264, 408, 328, 311, 64, 189, 700, 1157, 390, 335, 539, 1127, 807, 1550, 45, 645, 1428, 731, 11, 6, 242, 571, 929, 408, 425, 899, 685, 115, 31, 2771, 428, 386, 1600, 9519, 414, 2718, 1416, 2656, 5965]

theorem plane490GenLeaf0066 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0066Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0066Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0066Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0066Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 100
  · exact hroot.hOcc 111
  · exact hroot.hOcc 117
  · exact hroot.hOcc 119
  · exact hroot.hOcc 134
  · exact hroot.hOcc 151
  · exact hroot.hOcc 175
  · exact hroot.hOcc 193
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 202
  · exact hroot.hOcc 211
  · exact hroot.hOcc 219
  · exact hroot.hOcc 244
  · exact hroot.hOcc 263
  · exact hroot.hOcc 290
  · exact hroot.hOcc 295
  · exact hroot.hOcc 350
  · exact hroot.hOcc 375
  · exact hroot.hOcc 433
  · exact hroot.hOcc 460
  · exact hroot.hOcc 464
  · exact hroot.hOcc 468
  · exact hroot.hOcc 482
  · exact hroot.hOcc 542
  · exact hroot.hOcc 567
  · exact hroot.hOcc 575
  · exact hroot.hOcc 578
  · exact hroot.hOcc 621
  · exact hroot.hOcc 700
  · exact hroot.hOcc 706
  · exact hroot.hOcc 708
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
