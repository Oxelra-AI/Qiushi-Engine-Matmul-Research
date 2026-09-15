import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0043Refs : Fin 43 → RowRef 713 43 := ![.occ 91, .occ 104, .occ 107, .occ 113, .occ 114, .occ 144, .occ 169, .occ 174, .occ 198, .occ 201, .occ 203, .occ 238, .occ 255, .occ 290, .occ 314, .occ 347, .occ 354, .occ 358, .occ 382, .occ 460, .occ 468, .occ 518, .occ 533, .occ 557, .occ 595, .occ 605, .occ 641, .occ 662, .occ 684, .occ 704, .occ 706, .occ 710, .occ 712, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchGe 35 (1), .branchLe 42 (0), .branchLe 15 (0), .branchGe 36 (1)]

def plane490GenLeaf0043Mult : Fin 43 → Nat := ![9555, 39569, 5281, 4105, 3812, 2328, 4631, 7392, 10777, 5586, 4458, 24583, 2684, 6672, 1563, 3907, 19701, 8403, 14181, 8439, 12842, 8448, 5211, 7537, 7612, 8969, 5975, 2167, 823, 4906, 2167, 2521, 6478, 43903, 21453, 34241, 5662, 33341, 35464, 82241, 37129, 36830, 89846]

theorem plane490GenLeaf0043 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0043Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0043Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0043Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0043Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 104
  · exact hroot.hOcc 107
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 144
  · exact hroot.hOcc 169
  · exact hroot.hOcc 174
  · exact hroot.hOcc 198
  · exact hroot.hOcc 201
  · exact hroot.hOcc 203
  · exact hroot.hOcc 238
  · exact hroot.hOcc 255
  · exact hroot.hOcc 290
  · exact hroot.hOcc 314
  · exact hroot.hOcc 347
  · exact hroot.hOcc 354
  · exact hroot.hOcc 358
  · exact hroot.hOcc 382
  · exact hroot.hOcc 460
  · exact hroot.hOcc 468
  · exact hroot.hOcc 518
  · exact hroot.hOcc 533
  · exact hroot.hOcc 557
  · exact hroot.hOcc 595
  · exact hroot.hOcc 605
  · exact hroot.hOcc 641
  · exact hroot.hOcc 662
  · exact hroot.hOcc 684
  · exact hroot.hOcc 704
  · exact hroot.hOcc 706
  · exact hroot.hOcc 710
  · exact hroot.hOcc 712
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36

end QiushiMatmul
