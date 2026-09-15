import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0063Refs : Fin 43 → RowRef 713 43 := ![.occ 104, .occ 106, .occ 112, .occ 115, .occ 128, .occ 175, .occ 176, .occ 196, .occ 204, .occ 238, .occ 258, .occ 260, .occ 274, .occ 275, .occ 301, .occ 312, .occ 332, .occ 362, .occ 390, .occ 393, .occ 447, .occ 448, .occ 484, .occ 506, .occ 532, .occ 547, .occ 568, .occ 613, .occ 632, .occ 635, .occ 649, .occ 657, .occ 666, .occ 695, .sumGe, .nonneg 10, .branchLe 29 (0), .branchGe 4 (1), .branchLe 34 (0), .branchLe 23 (0), .branchGe 39 (1), .branchGe 18 (1), .branchGe 40 (1)]

def plane490GenLeaf0063Mult : Fin 43 → Nat := ![67, 178, 435, 539, 234, 543, 462, 116, 332, 64, 76, 67, 169, 435, 75, 312, 123, 398, 131, 68, 68, 104, 34, 47, 207, 9, 57, 34, 20, 35, 6, 30, 137, 98, 573, 79, 544, 2118, 509, 526, 795, 1466, 2272]

theorem plane490GenLeaf0063 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0063Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0063Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0063Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0063Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 112
  · exact hroot.hOcc 115
  · exact hroot.hOcc 128
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 196
  · exact hroot.hOcc 204
  · exact hroot.hOcc 238
  · exact hroot.hOcc 258
  · exact hroot.hOcc 260
  · exact hroot.hOcc 274
  · exact hroot.hOcc 275
  · exact hroot.hOcc 301
  · exact hroot.hOcc 312
  · exact hroot.hOcc 332
  · exact hroot.hOcc 362
  · exact hroot.hOcc 390
  · exact hroot.hOcc 393
  · exact hroot.hOcc 447
  · exact hroot.hOcc 448
  · exact hroot.hOcc 484
  · exact hroot.hOcc 506
  · exact hroot.hOcc 532
  · exact hroot.hOcc 547
  · exact hroot.hOcc 568
  · exact hroot.hOcc 613
  · exact hroot.hOcc 632
  · exact hroot.hOcc 635
  · exact hroot.hOcc 649
  · exact hroot.hOcc 657
  · exact hroot.hOcc 666
  · exact hroot.hOcc 695
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
