import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0054Refs : Fin 42 → RowRef 713 43 := ![.occ 91, .occ 106, .occ 140, .occ 146, .occ 171, .occ 180, .occ 191, .occ 195, .occ 198, .occ 209, .occ 210, .occ 219, .occ 230, .occ 252, .occ 284, .occ 291, .occ 302, .occ 314, .occ 334, .occ 338, .occ 353, .occ 364, .occ 370, .occ 379, .occ 389, .occ 452, .occ 459, .occ 460, .occ 461, .occ 610, .occ 620, .occ 649, .occ 674, .occ 710, .sumGe, .nonneg 40, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchGe 30 (1), .branchLe 6 (0), .branchGe 10 (1)]

def plane490GenLeaf0054Mult : Fin 42 → Nat := ![81, 55, 93, 20, 53, 109, 228, 24, 102, 18, 17, 63, 57, 87, 7, 86, 165, 104, 7, 5, 28, 188, 17, 6, 6, 56, 37, 111, 47, 134, 5, 41, 54, 43, 299, 36, 262, 184, 639, 884, 203, 548]

theorem plane490GenLeaf0054 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0054Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0054Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0054Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0054Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 106
  · exact hroot.hOcc 140
  · exact hroot.hOcc 146
  · exact hroot.hOcc 171
  · exact hroot.hOcc 180
  · exact hroot.hOcc 191
  · exact hroot.hOcc 195
  · exact hroot.hOcc 198
  · exact hroot.hOcc 209
  · exact hroot.hOcc 210
  · exact hroot.hOcc 219
  · exact hroot.hOcc 230
  · exact hroot.hOcc 252
  · exact hroot.hOcc 284
  · exact hroot.hOcc 291
  · exact hroot.hOcc 302
  · exact hroot.hOcc 314
  · exact hroot.hOcc 334
  · exact hroot.hOcc 338
  · exact hroot.hOcc 353
  · exact hroot.hOcc 364
  · exact hroot.hOcc 370
  · exact hroot.hOcc 379
  · exact hroot.hOcc 389
  · exact hroot.hOcc 452
  · exact hroot.hOcc 459
  · exact hroot.hOcc 460
  · exact hroot.hOcc 461
  · exact hroot.hOcc 610
  · exact hroot.hOcc 620
  · exact hroot.hOcc 649
  · exact hroot.hOcc 674
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
