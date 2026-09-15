import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0036Refs : Fin 43 → RowRef 713 43 := ![.occ 87, .occ 95, .occ 114, .occ 137, .occ 181, .occ 184, .occ 209, .occ 219, .occ 252, .occ 283, .occ 302, .occ 303, .occ 336, .occ 354, .occ 377, .occ 411, .occ 423, .occ 442, .occ 460, .occ 461, .occ 462, .occ 487, .occ 491, .occ 494, .occ 506, .occ 516, .occ 533, .occ 574, .occ 609, .occ 679, .occ 701, .occ 704, .sumGe, .nonneg 9, .nonneg 30, .nonneg 32, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 28 (0), .branchLe 35 (0), .branchLe 5 (0), .branchGe 38 (1)]

def plane490GenLeaf0036Mult : Fin 43 → Nat := ![203, 71, 715, 475, 797, 1672, 98, 213, 486, 359, 1180, 98, 984, 287, 882, 218, 31, 294, 41, 639, 666, 107, 18, 309, 205, 204, 298, 11, 230, 205, 85, 78, 1672, 30, 667, 559, 1587, 1565, 5398, 965, 788, 1150, 6544]

theorem plane490GenLeaf0036 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0036Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0036Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0036Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0036Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 95
  · exact hroot.hOcc 114
  · exact hroot.hOcc 137
  · exact hroot.hOcc 181
  · exact hroot.hOcc 184
  · exact hroot.hOcc 209
  · exact hroot.hOcc 219
  · exact hroot.hOcc 252
  · exact hroot.hOcc 283
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 336
  · exact hroot.hOcc 354
  · exact hroot.hOcc 377
  · exact hroot.hOcc 411
  · exact hroot.hOcc 423
  · exact hroot.hOcc 442
  · exact hroot.hOcc 460
  · exact hroot.hOcc 461
  · exact hroot.hOcc 462
  · exact hroot.hOcc 487
  · exact hroot.hOcc 491
  · exact hroot.hOcc 494
  · exact hroot.hOcc 506
  · exact hroot.hOcc 516
  · exact hroot.hOcc 533
  · exact hroot.hOcc 574
  · exact hroot.hOcc 609
  · exact hroot.hOcc 679
  · exact hroot.hOcc 701
  · exact hroot.hOcc 704
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
