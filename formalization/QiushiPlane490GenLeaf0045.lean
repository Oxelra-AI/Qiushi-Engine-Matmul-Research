import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0045Refs : Fin 44 → RowRef 713 43 := ![.occ 93, .occ 95, .occ 104, .occ 110, .occ 113, .occ 131, .occ 162, .occ 198, .occ 236, .occ 238, .occ 292, .occ 302, .occ 303, .occ 352, .occ 359, .occ 379, .occ 422, .occ 447, .occ 449, .occ 453, .occ 454, .occ 460, .occ 468, .occ 480, .occ 486, .occ 516, .occ 519, .occ 599, .occ 617, .occ 661, .occ 662, .occ 665, .occ 666, .occ 704, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchGe 35 (1), .branchLe 42 (0), .branchGe 15 (1), .branchGe 0 (1)]

def plane490GenLeaf0045Mult : Fin 44 → Nat := ![86, 105, 146, 68, 169, 89, 117, 65, 154, 49, 211, 83, 127, 28, 33, 325, 163, 7, 71, 18, 114, 22, 32, 16, 82, 33, 113, 4, 90, 13, 66, 60, 12, 10, 335, 335, 335, 817, 335, 61, 796, 247, 1026, 999]

theorem plane490GenLeaf0045 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0045Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0045Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0045Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0045Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 104
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 131
  · exact hroot.hOcc 162
  · exact hroot.hOcc 198
  · exact hroot.hOcc 236
  · exact hroot.hOcc 238
  · exact hroot.hOcc 292
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 352
  · exact hroot.hOcc 359
  · exact hroot.hOcc 379
  · exact hroot.hOcc 422
  · exact hroot.hOcc 447
  · exact hroot.hOcc 449
  · exact hroot.hOcc 453
  · exact hroot.hOcc 454
  · exact hroot.hOcc 460
  · exact hroot.hOcc 468
  · exact hroot.hOcc 480
  · exact hroot.hOcc 486
  · exact hroot.hOcc 516
  · exact hroot.hOcc 519
  · exact hroot.hOcc 599
  · exact hroot.hOcc 617
  · exact hroot.hOcc 661
  · exact hroot.hOcc 662
  · exact hroot.hOcc 665
  · exact hroot.hOcc 666
  · exact hroot.hOcc 704
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
