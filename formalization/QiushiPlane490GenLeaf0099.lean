import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0099Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 94, .occ 95, .occ 105, .occ 106, .occ 108, .occ 114, .occ 142, .occ 146, .occ 165, .occ 198, .occ 211, .occ 234, .occ 248, .occ 250, .occ 271, .occ 281, .occ 284, .occ 291, .occ 299, .occ 303, .occ 312, .occ 321, .occ 349, .occ 395, .occ 460, .occ 473, .occ 514, .occ 526, .occ 538, .occ 551, .occ 562, .occ 582, .occ 602, .occ 668, .occ 686, .sumGe, .nonneg 38, .branchGe 29 (1), .branchGe 18 (1), .branchLe 14 (0), .branchLe 1 (0), .branchGe 21 (1), .branchLe 8 (0)]

def plane490GenLeaf0099Mult : Fin 44 → Nat := ![1565, 712, 2182, 1725, 388, 1104, 1715, 1711, 2649, 1327, 617, 588, 209, 2734, 1924, 204, 710, 1213, 2208, 507, 3599, 264, 1621, 1433, 443, 1268, 1391, 591, 1004, 801, 1446, 781, 1621, 591, 736, 104, 5727, 1943, 10610, 7352, 4281, 5727, 18046, 5727]

theorem plane490GenLeaf0099 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0099Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0099Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0099Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0099Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 114
  · exact hroot.hOcc 142
  · exact hroot.hOcc 146
  · exact hroot.hOcc 165
  · exact hroot.hOcc 198
  · exact hroot.hOcc 211
  · exact hroot.hOcc 234
  · exact hroot.hOcc 248
  · exact hroot.hOcc 250
  · exact hroot.hOcc 271
  · exact hroot.hOcc 281
  · exact hroot.hOcc 284
  · exact hroot.hOcc 291
  · exact hroot.hOcc 299
  · exact hroot.hOcc 303
  · exact hroot.hOcc 312
  · exact hroot.hOcc 321
  · exact hroot.hOcc 349
  · exact hroot.hOcc 395
  · exact hroot.hOcc 460
  · exact hroot.hOcc 473
  · exact hroot.hOcc 514
  · exact hroot.hOcc 526
  · exact hroot.hOcc 538
  · exact hroot.hOcc 551
  · exact hroot.hOcc 562
  · exact hroot.hOcc 582
  · exact hroot.hOcc 602
  · exact hroot.hOcc 668
  · exact hroot.hOcc 686
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8

end QiushiMatmul
