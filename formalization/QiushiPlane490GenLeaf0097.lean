import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0097Refs : Fin 44 → RowRef 713 43 := ![.occ 104, .occ 106, .occ 108, .occ 116, .occ 159, .occ 171, .occ 172, .occ 203, .occ 224, .occ 228, .occ 239, .occ 284, .occ 312, .occ 332, .occ 335, .occ 345, .occ 349, .occ 375, .occ 395, .occ 494, .occ 519, .occ 521, .occ 522, .occ 523, .occ 538, .occ 543, .occ 546, .occ 562, .occ 582, .occ 587, .occ 588, .occ 602, .occ 632, .occ 642, .occ 679, .occ 686, .sumGe, .branchGe 29 (1), .branchGe 18 (1), .branchLe 14 (0), .branchLe 1 (0), .branchLe 21 (0), .branchLe 3 (0), .branchGe 20 (1)]

def plane490GenLeaf0097Mult : Fin 44 → Nat := ![44460, 28152, 44023, 2298, 18791, 4318, 3029, 1428, 1095, 2621, 2277, 871, 5010, 30012, 7390, 324, 10601, 558, 727, 38262, 1697, 1226, 2111, 16514, 1598, 7018, 1192, 36199, 5995, 134, 16404, 8405, 1405, 1595, 792, 4129, 48944, 90580, 123319, 45819, 48944, 48944, 45149, 187007]

theorem plane490GenLeaf0097 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0097Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0097Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0097Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0097Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 116
  · exact hroot.hOcc 159
  · exact hroot.hOcc 171
  · exact hroot.hOcc 172
  · exact hroot.hOcc 203
  · exact hroot.hOcc 224
  · exact hroot.hOcc 228
  · exact hroot.hOcc 239
  · exact hroot.hOcc 284
  · exact hroot.hOcc 312
  · exact hroot.hOcc 332
  · exact hroot.hOcc 335
  · exact hroot.hOcc 345
  · exact hroot.hOcc 349
  · exact hroot.hOcc 375
  · exact hroot.hOcc 395
  · exact hroot.hOcc 494
  · exact hroot.hOcc 519
  · exact hroot.hOcc 521
  · exact hroot.hOcc 522
  · exact hroot.hOcc 523
  · exact hroot.hOcc 538
  · exact hroot.hOcc 543
  · exact hroot.hOcc 546
  · exact hroot.hOcc 562
  · exact hroot.hOcc 582
  · exact hroot.hOcc 587
  · exact hroot.hOcc 588
  · exact hroot.hOcc 602
  · exact hroot.hOcc 632
  · exact hroot.hOcc 642
  · exact hroot.hOcc 679
  · exact hroot.hOcc 686
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
