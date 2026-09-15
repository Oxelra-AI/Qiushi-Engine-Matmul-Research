import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0049Refs : Fin 43 → RowRef 713 43 := ![.occ 89, .occ 116, .occ 147, .occ 154, .occ 164, .occ 201, .occ 222, .occ 234, .occ 237, .occ 271, .occ 272, .occ 280, .occ 295, .occ 302, .occ 309, .occ 333, .occ 335, .occ 346, .occ 362, .occ 379, .occ 506, .occ 510, .occ 511, .occ 534, .occ 549, .occ 575, .occ 602, .occ 617, .occ 627, .occ 670, .occ 681, .occ 709, .sumGe, .nonneg 17, .nonneg 38, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchGe 28 (1), .branchLe 39 (0), .branchLe 21 (0), .branchGe 33 (1)]

def plane490GenLeaf0049Mult : Fin 43 → Nat := ![106, 184, 345, 199, 285, 181, 172, 271, 209, 131, 137, 50, 150, 232, 8, 132, 220, 58, 208, 45, 19, 86, 16, 40, 12, 191, 46, 40, 70, 31, 41, 56, 508, 12, 12, 107, 256, 837, 413, 1597, 477, 18, 1366]

theorem plane490GenLeaf0049 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0049Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0049Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0049Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0049Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 116
  · exact hroot.hOcc 147
  · exact hroot.hOcc 154
  · exact hroot.hOcc 164
  · exact hroot.hOcc 201
  · exact hroot.hOcc 222
  · exact hroot.hOcc 234
  · exact hroot.hOcc 237
  · exact hroot.hOcc 271
  · exact hroot.hOcc 272
  · exact hroot.hOcc 280
  · exact hroot.hOcc 295
  · exact hroot.hOcc 302
  · exact hroot.hOcc 309
  · exact hroot.hOcc 333
  · exact hroot.hOcc 335
  · exact hroot.hOcc 346
  · exact hroot.hOcc 362
  · exact hroot.hOcc 379
  · exact hroot.hOcc 506
  · exact hroot.hOcc 510
  · exact hroot.hOcc 511
  · exact hroot.hOcc 534
  · exact hroot.hOcc 549
  · exact hroot.hOcc 575
  · exact hroot.hOcc 602
  · exact hroot.hOcc 617
  · exact hroot.hOcc 627
  · exact hroot.hOcc 670
  · exact hroot.hOcc 681
  · exact hroot.hOcc 709
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
