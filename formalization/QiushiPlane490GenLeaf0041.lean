import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0041Refs : Fin 44 → RowRef 713 43 := ![.occ 91, .occ 93, .occ 104, .occ 113, .occ 114, .occ 169, .occ 201, .occ 203, .occ 205, .occ 228, .occ 260, .occ 268, .occ 272, .occ 302, .occ 326, .occ 343, .occ 358, .occ 359, .occ 362, .occ 368, .occ 369, .occ 375, .occ 382, .occ 460, .occ 467, .occ 498, .occ 499, .occ 520, .occ 522, .occ 617, .occ 645, .occ 662, .occ 712, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchGe 35 (1), .branchLe 42 (0), .branchLe 15 (0), .branchLe 36 (0), .branchLe 3 (0)]

def plane490GenLeaf0041Mult : Fin 44 → Nat := ![7541, 1327, 6398, 8145, 7392, 7678, 5617, 822, 2975, 1300, 3786, 2723, 4151, 7118, 1565, 204, 4231, 22, 4226, 3189, 286, 1898, 1402, 7882, 5159, 5503, 1219, 875, 679, 143, 540, 2224, 205, 15814, 15609, 15814, 13374, 14930, 1808, 36096, 15814, 14939, 10450, 15814]

theorem plane490GenLeaf0041 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0041Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0041Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0041Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0041Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 93
  · exact hroot.hOcc 104
  · exact hroot.hOcc 113
  · exact hroot.hOcc 114
  · exact hroot.hOcc 169
  · exact hroot.hOcc 201
  · exact hroot.hOcc 203
  · exact hroot.hOcc 205
  · exact hroot.hOcc 228
  · exact hroot.hOcc 260
  · exact hroot.hOcc 268
  · exact hroot.hOcc 272
  · exact hroot.hOcc 302
  · exact hroot.hOcc 326
  · exact hroot.hOcc 343
  · exact hroot.hOcc 358
  · exact hroot.hOcc 359
  · exact hroot.hOcc 362
  · exact hroot.hOcc 368
  · exact hroot.hOcc 369
  · exact hroot.hOcc 375
  · exact hroot.hOcc 382
  · exact hroot.hOcc 460
  · exact hroot.hOcc 467
  · exact hroot.hOcc 498
  · exact hroot.hOcc 499
  · exact hroot.hOcc 520
  · exact hroot.hOcc 522
  · exact hroot.hOcc 617
  · exact hroot.hOcc 645
  · exact hroot.hOcc 662
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
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3

end QiushiMatmul
