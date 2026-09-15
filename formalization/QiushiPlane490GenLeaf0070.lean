import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0070Refs : Fin 43 → RowRef 713 43 := ![.occ 86, .occ 90, .occ 107, .occ 110, .occ 115, .occ 195, .occ 202, .occ 204, .occ 216, .occ 219, .occ 226, .occ 236, .occ 238, .occ 264, .occ 274, .occ 290, .occ 295, .occ 302, .occ 333, .occ 335, .occ 350, .occ 421, .occ 506, .occ 525, .occ 542, .occ 571, .occ 572, .occ 575, .occ 580, .occ 617, .occ 657, .occ 662, .occ 670, .occ 698, .sumGe, .nonneg 20, .nonneg 34, .nonneg 38, .branchLe 29 (0), .branchGe 4 (1), .branchGe 23 (1), .branchGe 25 (1), .branchGe 33 (1)]

def plane490GenLeaf0070Mult : Fin 43 → Nat := ![40, 634, 1575, 384, 365, 760, 84, 1182, 23, 12, 50, 118, 317, 889, 1316, 1481, 1173, 58, 317, 1834, 2184, 325, 1401, 688, 460, 247, 97, 543, 31, 1204, 976, 317, 831, 189, 3208, 193, 642, 1552, 2891, 8276, 4815, 5699, 8160]

theorem plane490GenLeaf0070 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0070Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0070Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0070Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0070Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 86
  · exact hroot.hOcc 90
  · exact hroot.hOcc 107
  · exact hroot.hOcc 110
  · exact hroot.hOcc 115
  · exact hroot.hOcc 195
  · exact hroot.hOcc 202
  · exact hroot.hOcc 204
  · exact hroot.hOcc 216
  · exact hroot.hOcc 219
  · exact hroot.hOcc 226
  · exact hroot.hOcc 236
  · exact hroot.hOcc 238
  · exact hroot.hOcc 264
  · exact hroot.hOcc 274
  · exact hroot.hOcc 290
  · exact hroot.hOcc 295
  · exact hroot.hOcc 302
  · exact hroot.hOcc 333
  · exact hroot.hOcc 335
  · exact hroot.hOcc 350
  · exact hroot.hOcc 421
  · exact hroot.hOcc 506
  · exact hroot.hOcc 525
  · exact hroot.hOcc 542
  · exact hroot.hOcc 571
  · exact hroot.hOcc 572
  · exact hroot.hOcc 575
  · exact hroot.hOcc 580
  · exact hroot.hOcc 617
  · exact hroot.hOcc 657
  · exact hroot.hOcc 662
  · exact hroot.hOcc 670
  · exact hroot.hOcc 698
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
