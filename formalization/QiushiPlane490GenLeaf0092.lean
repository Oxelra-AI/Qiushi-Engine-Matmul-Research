import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0092Refs : Fin 42 → RowRef 713 43 := ![.occ 93, .occ 95, .occ 105, .occ 108, .occ 112, .occ 113, .occ 119, .occ 120, .occ 139, .occ 152, .occ 161, .occ 170, .occ 203, .occ 211, .occ 219, .occ 239, .occ 247, .occ 252, .occ 274, .occ 283, .occ 284, .occ 295, .occ 297, .occ 302, .occ 303, .occ 336, .occ 362, .occ 438, .occ 475, .occ 525, .occ 636, .occ 669, .occ 673, .occ 701, .occ 706, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchGe 22 (1), .branchLe 3 (0), .branchGe 2 (1)]

def plane490GenLeaf0092Mult : Fin 42 → Nat := ![1424, 398, 1142, 930, 741, 740, 98, 677, 263, 855, 781, 1463, 905, 500, 58, 361, 147, 533, 53, 93, 42, 306, 261, 263, 121, 20, 400, 70, 22, 39, 508, 20, 702, 253, 282, 1463, 4469, 781, 987, 4040, 644, 4642]

theorem plane490GenLeaf0092 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0092Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0092Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0092Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0092Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 139
  · exact hroot.hOcc 152
  · exact hroot.hOcc 161
  · exact hroot.hOcc 170
  · exact hroot.hOcc 203
  · exact hroot.hOcc 211
  · exact hroot.hOcc 219
  · exact hroot.hOcc 239
  · exact hroot.hOcc 247
  · exact hroot.hOcc 252
  · exact hroot.hOcc 274
  · exact hroot.hOcc 283
  · exact hroot.hOcc 284
  · exact hroot.hOcc 295
  · exact hroot.hOcc 297
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 336
  · exact hroot.hOcc 362
  · exact hroot.hOcc 438
  · exact hroot.hOcc 475
  · exact hroot.hOcc 525
  · exact hroot.hOcc 636
  · exact hroot.hOcc 669
  · exact hroot.hOcc 673
  · exact hroot.hOcc 701
  · exact hroot.hOcc 706
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
