import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0112Refs : Fin 44 → RowRef 713 43 := ![.occ 99, .occ 100, .occ 105, .occ 106, .occ 107, .occ 108, .occ 133, .occ 139, .occ 147, .occ 164, .occ 178, .occ 205, .occ 225, .occ 258, .occ 290, .occ 300, .occ 336, .occ 339, .occ 364, .occ 365, .occ 391, .occ 437, .occ 447, .occ 450, .occ 486, .occ 515, .occ 521, .occ 562, .occ 590, .occ 601, .occ 602, .occ 607, .occ 649, .occ 651, .occ 670, .sumGe, .nonneg 4, .nonneg 30, .branchGe 29 (1), .branchGe 18 (1), .branchGe 14 (1), .branchLe 32 (0), .branchLe 38 (0), .branchGe 25 (1)]

def plane490GenLeaf0112Mult : Fin 44 → Nat := ![7383, 6318, 12485, 2894, 8135, 11009, 10832, 12605, 1970, 2062, 1775, 2236, 2312, 1678, 6358, 9502, 255, 1855, 6032, 2528, 2802, 2744, 2665, 2449, 537, 467, 301, 3129, 1042, 1596, 4350, 661, 2796, 120, 1236, 12605, 847, 828, 29851, 20909, 41960, 12605, 12605, 40253]

theorem plane490GenLeaf0112 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0112Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0112Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0112Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0112Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 133
  · exact hroot.hOcc 139
  · exact hroot.hOcc 147
  · exact hroot.hOcc 164
  · exact hroot.hOcc 178
  · exact hroot.hOcc 205
  · exact hroot.hOcc 225
  · exact hroot.hOcc 258
  · exact hroot.hOcc 290
  · exact hroot.hOcc 300
  · exact hroot.hOcc 336
  · exact hroot.hOcc 339
  · exact hroot.hOcc 364
  · exact hroot.hOcc 365
  · exact hroot.hOcc 391
  · exact hroot.hOcc 437
  · exact hroot.hOcc 447
  · exact hroot.hOcc 450
  · exact hroot.hOcc 486
  · exact hroot.hOcc 515
  · exact hroot.hOcc 521
  · exact hroot.hOcc 562
  · exact hroot.hOcc 590
  · exact hroot.hOcc 601
  · exact hroot.hOcc 602
  · exact hroot.hOcc 607
  · exact hroot.hOcc 649
  · exact hroot.hOcc 651
  · exact hroot.hOcc 670
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
