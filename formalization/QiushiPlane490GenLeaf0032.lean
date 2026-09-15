import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0032Refs : Fin 43 → RowRef 713 43 := ![.occ 85, .occ 91, .occ 94, .occ 95, .occ 109, .occ 202, .occ 219, .occ 270, .occ 272, .occ 292, .occ 303, .occ 354, .occ 362, .occ 379, .occ 486, .occ 494, .occ 509, .occ 518, .occ 522, .occ 535, .occ 542, .occ 578, .occ 607, .occ 641, .occ 648, .occ 649, .occ 664, .occ 665, .occ 679, .sumGe, .nonneg 3, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchLe 35 (0), .branchLe 5 (0), .branchLe 38 (0), .branchLe 25 (0), .branchGe 15 (1), .branchLe 14 (0), .branchGe 24 (1)]

def plane490GenLeaf0032Mult : Fin 43 → Nat := ![33, 1, 33, 63, 48, 8, 19, 16, 17, 22, 100, 41, 115, 33, 30, 19, 33, 14, 2, 53, 4, 1, 63, 11, 4, 17, 49, 14, 74, 167, 9, 71, 154, 105, 144, 22, 153, 137, 107, 8, 176, 118, 488]

theorem plane490GenLeaf0032 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0032Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0032Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0032Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0032Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 109
  · exact hroot.hOcc 202
  · exact hroot.hOcc 219
  · exact hroot.hOcc 270
  · exact hroot.hOcc 272
  · exact hroot.hOcc 292
  · exact hroot.hOcc 303
  · exact hroot.hOcc 354
  · exact hroot.hOcc 362
  · exact hroot.hOcc 379
  · exact hroot.hOcc 486
  · exact hroot.hOcc 494
  · exact hroot.hOcc 509
  · exact hroot.hOcc 518
  · exact hroot.hOcc 522
  · exact hroot.hOcc 535
  · exact hroot.hOcc 542
  · exact hroot.hOcc 578
  · exact hroot.hOcc 607
  · exact hroot.hOcc 641
  · exact hroot.hOcc 648
  · exact hroot.hOcc 649
  · exact hroot.hOcc 664
  · exact hroot.hOcc 665
  · exact hroot.hOcc 679
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
