import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0042Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 90, .occ 99, .occ 103, .occ 104, .occ 113, .occ 114, .occ 133, .occ 137, .occ 169, .occ 205, .occ 236, .occ 260, .occ 272, .occ 279, .occ 302, .occ 326, .occ 336, .occ 343, .occ 369, .occ 431, .occ 453, .occ 460, .occ 467, .occ 486, .occ 498, .occ 553, .occ 599, .occ 617, .occ 626, .occ 627, .occ 706, .occ 712, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchGe 35 (1), .branchLe 42 (0), .branchLe 15 (0), .branchLe 36 (0), .branchGe 3 (1)]

def plane490GenLeaf0042Mult : Fin 44 → Nat := ![7907, 7542, 111, 129, 4351, 3891, 256, 1143, 6192, 1017, 2651, 1209, 314, 1171, 242, 3406, 1744, 2195, 3013, 385, 1561, 2087, 2233, 1976, 989, 1506, 736, 412, 2049, 149, 726, 1193, 365, 7907, 6806, 6714, 16104, 5347, 2750, 12440, 4976, 5725, 5566, 21125]

theorem plane490GenLeaf0042 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0042Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0042Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0042Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0042Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 133
  · exact hroot.hOcc 137
  · exact hroot.hOcc 169
  · exact hroot.hOcc 205
  · exact hroot.hOcc 236
  · exact hroot.hOcc 260
  · exact hroot.hOcc 272
  · exact hroot.hOcc 279
  · exact hroot.hOcc 302
  · exact hroot.hOcc 326
  · exact hroot.hOcc 336
  · exact hroot.hOcc 343
  · exact hroot.hOcc 369
  · exact hroot.hOcc 431
  · exact hroot.hOcc 453
  · exact hroot.hOcc 460
  · exact hroot.hOcc 467
  · exact hroot.hOcc 486
  · exact hroot.hOcc 498
  · exact hroot.hOcc 553
  · exact hroot.hOcc 599
  · exact hroot.hOcc 617
  · exact hroot.hOcc 626
  · exact hroot.hOcc 627
  · exact hroot.hOcc 706
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
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
