import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0044Refs : Fin 44 → RowRef 713 43 := ![.occ 90, .occ 93, .occ 104, .occ 110, .occ 113, .occ 114, .occ 117, .occ 127, .occ 131, .occ 238, .occ 268, .occ 271, .occ 302, .occ 303, .occ 340, .occ 343, .occ 358, .occ 359, .occ 369, .occ 382, .occ 417, .occ 447, .occ 449, .occ 453, .occ 468, .occ 519, .occ 520, .occ 586, .occ 613, .occ 617, .occ 633, .occ 643, .occ 648, .occ 679, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchGe 35 (1), .branchLe 42 (0), .branchGe 15 (1), .branchLe 0 (0)]

def plane490GenLeaf0044Mult : Fin 44 → Nat := ![853, 855, 2184, 1, 699, 279, 895, 98, 1287, 1124, 449, 851, 1338, 1552, 43, 1176, 333, 1637, 18, 2099, 566, 257, 170, 440, 683, 451, 1101, 194, 119, 469, 352, 245, 610, 257, 3359, 3359, 3359, 2419, 2793, 3165, 8804, 3359, 3351, 3359]

theorem plane490GenLeaf0044 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0044Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0044Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0044Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0044Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 104
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 117
  · exact hroot.hOcc 127
  · exact hroot.hOcc 131
  · exact hroot.hOcc 238
  · exact hroot.hOcc 268
  · exact hroot.hOcc 271
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 340
  · exact hroot.hOcc 343
  · exact hroot.hOcc 358
  · exact hroot.hOcc 359
  · exact hroot.hOcc 369
  · exact hroot.hOcc 382
  · exact hroot.hOcc 417
  · exact hroot.hOcc 447
  · exact hroot.hOcc 449
  · exact hroot.hOcc 453
  · exact hroot.hOcc 468
  · exact hroot.hOcc 519
  · exact hroot.hOcc 520
  · exact hroot.hOcc 586
  · exact hroot.hOcc 613
  · exact hroot.hOcc 617
  · exact hroot.hOcc 633
  · exact hroot.hOcc 643
  · exact hroot.hOcc 648
  · exact hroot.hOcc 679
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
