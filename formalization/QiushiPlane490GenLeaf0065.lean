import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0065Refs : Fin 44 → RowRef 713 43 := ![.occ 91, .occ 104, .occ 115, .occ 151, .occ 195, .occ 196, .occ 202, .occ 203, .occ 219, .occ 252, .occ 274, .occ 280, .occ 295, .occ 314, .occ 335, .occ 350, .occ 359, .occ 364, .occ 372, .occ 376, .occ 384, .occ 409, .occ 459, .occ 461, .occ 468, .occ 482, .occ 506, .occ 527, .occ 542, .occ 569, .occ 579, .occ 670, .occ 689, .occ 700, .sumGe, .nonneg 3, .branchLe 29 (0), .branchGe 4 (1), .branchLe 34 (0), .branchGe 23 (1), .branchLe 25 (0), .branchLe 18 (0), .branchLe 21 (0), .branchGe 11 (1)]

def plane490GenLeaf0065Mult : Fin 44 → Nat := ![4754, 2289, 4629, 2108, 3016, 1614, 1374, 1191, 1153, 1001, 314, 612, 148, 1822, 1564, 831, 756, 193, 519, 1311, 623, 1281, 1274, 106, 189, 232, 1818, 648, 2175, 276, 536, 1830, 1351, 69, 6197, 52, 4691, 12406, 4698, 7183, 4319, 4379, 6049, 15113]

theorem plane490GenLeaf0065 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0065Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0065Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0065Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0065Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 104
  · exact hroot.hOcc 115
  · exact hroot.hOcc 151
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 202
  · exact hroot.hOcc 203
  · exact hroot.hOcc 219
  · exact hroot.hOcc 252
  · exact hroot.hOcc 274
  · exact hroot.hOcc 280
  · exact hroot.hOcc 295
  · exact hroot.hOcc 314
  · exact hroot.hOcc 335
  · exact hroot.hOcc 350
  · exact hroot.hOcc 359
  · exact hroot.hOcc 364
  · exact hroot.hOcc 372
  · exact hroot.hOcc 376
  · exact hroot.hOcc 384
  · exact hroot.hOcc 409
  · exact hroot.hOcc 459
  · exact hroot.hOcc 461
  · exact hroot.hOcc 468
  · exact hroot.hOcc 482
  · exact hroot.hOcc 506
  · exact hroot.hOcc 527
  · exact hroot.hOcc 542
  · exact hroot.hOcc 569
  · exact hroot.hOcc 579
  · exact hroot.hOcc 670
  · exact hroot.hOcc 689
  · exact hroot.hOcc 700
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
