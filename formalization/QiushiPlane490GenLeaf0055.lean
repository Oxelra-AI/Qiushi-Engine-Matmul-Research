import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0055Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 110, .occ 134, .occ 148, .occ 150, .occ 164, .occ 165, .occ 191, .occ 219, .occ 233, .occ 237, .occ 247, .occ 250, .occ 272, .occ 280, .occ 289, .occ 291, .occ 302, .occ 326, .occ 336, .occ 364, .occ 383, .occ 449, .occ 454, .occ 457, .occ 472, .occ 478, .occ 522, .occ 586, .occ 610, .occ 617, .occ 629, .occ 668, .occ 679, .occ 704, .sumGe, .nonneg 40, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchGe 30 (1), .branchGe 6 (1), .branchLe 22 (0), .branchLe 39 (0)]

def plane490GenLeaf0055Mult : Fin 44 → Nat := ![1096, 907, 3267, 11000, 5159, 8515, 1348, 24778, 6391, 5270, 6874, 10069, 151, 256, 594, 2846, 6198, 9064, 370, 18400, 243, 486, 679, 5456, 1934, 7772, 180, 3709, 436, 4050, 9516, 6047, 5955, 8388, 63, 24778, 1700, 16675, 18580, 94056, 78734, 20580, 14709, 24715]

theorem plane490GenLeaf0055 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0055Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0055Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0055Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0055Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 110
  · exact hroot.hOcc 134
  · exact hroot.hOcc 148
  · exact hroot.hOcc 150
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 191
  · exact hroot.hOcc 219
  · exact hroot.hOcc 233
  · exact hroot.hOcc 237
  · exact hroot.hOcc 247
  · exact hroot.hOcc 250
  · exact hroot.hOcc 272
  · exact hroot.hOcc 280
  · exact hroot.hOcc 289
  · exact hroot.hOcc 291
  · exact hroot.hOcc 302
  · exact hroot.hOcc 326
  · exact hroot.hOcc 336
  · exact hroot.hOcc 364
  · exact hroot.hOcc 383
  · exact hroot.hOcc 449
  · exact hroot.hOcc 454
  · exact hroot.hOcc 457
  · exact hroot.hOcc 472
  · exact hroot.hOcc 478
  · exact hroot.hOcc 522
  · exact hroot.hOcc 586
  · exact hroot.hOcc 610
  · exact hroot.hOcc 617
  · exact hroot.hOcc 629
  · exact hroot.hOcc 668
  · exact hroot.hOcc 679
  · exact hroot.hOcc 704
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39

end QiushiMatmul
