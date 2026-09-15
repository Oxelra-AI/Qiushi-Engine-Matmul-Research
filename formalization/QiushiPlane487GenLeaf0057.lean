import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0057Refs : Fin 49 → RowRef 668 48 := ![.occ 85, .occ 99, .occ 136, .occ 160, .occ 188, .occ 195, .occ 196, .occ 213, .occ 219, .occ 234, .occ 235, .occ 246, .occ 260, .occ 265, .occ 302, .occ 313, .occ 315, .occ 322, .occ 351, .occ 386, .occ 390, .occ 394, .occ 429, .occ 470, .occ 549, .occ 566, .occ 578, .occ 595, .occ 602, .occ 612, .occ 620, .occ 644, .occ 645, .occ 650, .occ 660, .sumGe, .nonneg 42, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 19 (0), .branchLe 36 (0), .branchGe 23 (1), .branchLe 10 (0), .branchLe 16 (0), .branchLe 20 (0), .branchLe 33 (0)]

def plane487GenLeaf0057Mult : Fin 49 → Nat := ![2606, 24624, 6622, 9889, 745, 15491, 3680, 13447, 3838, 10234, 16434, 3341, 9619, 11246, 6485, 8728, 1922, 1689, 42976, 2681, 5871, 2681, 12765, 17528, 928, 2062, 7819, 5613, 2443, 10965, 12659, 12494, 6413, 5497, 146, 52084, 3924, 109949, 3845, 46576, 37994, 19869, 50162, 23188, 112561, 39444, 23558, 45671, 51938]

theorem plane487GenLeaf0057 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0057Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0057Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0057Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0057Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 99
  · exact hroot.hOcc 136
  · exact hroot.hOcc 160
  · exact hroot.hOcc 188
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 213
  · exact hroot.hOcc 219
  · exact hroot.hOcc 234
  · exact hroot.hOcc 235
  · exact hroot.hOcc 246
  · exact hroot.hOcc 260
  · exact hroot.hOcc 265
  · exact hroot.hOcc 302
  · exact hroot.hOcc 313
  · exact hroot.hOcc 315
  · exact hroot.hOcc 322
  · exact hroot.hOcc 351
  · exact hroot.hOcc 386
  · exact hroot.hOcc 390
  · exact hroot.hOcc 394
  · exact hroot.hOcc 429
  · exact hroot.hOcc 470
  · exact hroot.hOcc 549
  · exact hroot.hOcc 566
  · exact hroot.hOcc 578
  · exact hroot.hOcc 595
  · exact hroot.hOcc 602
  · exact hroot.hOcc 612
  · exact hroot.hOcc 620
  · exact hroot.hOcc 644
  · exact hroot.hOcc 645
  · exact hroot.hOcc 650
  · exact hroot.hOcc 660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (42 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (23 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (10 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (16 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (20 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (33 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33

end QiushiMatmul
