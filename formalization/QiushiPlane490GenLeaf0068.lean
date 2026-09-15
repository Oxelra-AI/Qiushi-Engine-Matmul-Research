import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0068Refs : Fin 44 → RowRef 713 43 := ![.occ 91, .occ 93, .occ 99, .occ 107, .occ 115, .occ 119, .occ 139, .occ 140, .occ 175, .occ 184, .occ 190, .occ 204, .occ 211, .occ 216, .occ 236, .occ 258, .occ 264, .occ 268, .occ 274, .occ 336, .occ 350, .occ 433, .occ 436, .occ 453, .occ 503, .occ 533, .occ 542, .occ 571, .occ 572, .occ 614, .occ 623, .occ 661, .occ 666, .occ 673, .occ 697, .occ 700, .sumGe, .branchLe 29 (0), .branchGe 4 (1), .branchLe 34 (0), .branchGe 23 (1), .branchGe 25 (1), .branchLe 33 (0), .branchLe 5 (0)]

def plane490GenLeaf0068Mult : Fin 44 → Nat := ![562, 423, 2086, 1909, 1892, 1219, 1378, 2780, 689, 394, 117, 204, 177, 1173, 1132, 892, 1389, 183, 1179, 189, 279, 604, 243, 22, 685, 205, 1218, 108, 262, 315, 1207, 229, 434, 75, 398, 1003, 3293, 2895, 9108, 3293, 4872, 11999, 3293, 3293]

theorem plane490GenLeaf0068 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0068Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0068Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0068Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0068Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 93
  · exact hroot.hOcc 99
  · exact hroot.hOcc 107
  · exact hroot.hOcc 115
  · exact hroot.hOcc 119
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 175
  · exact hroot.hOcc 184
  · exact hroot.hOcc 190
  · exact hroot.hOcc 204
  · exact hroot.hOcc 211
  · exact hroot.hOcc 216
  · exact hroot.hOcc 236
  · exact hroot.hOcc 258
  · exact hroot.hOcc 264
  · exact hroot.hOcc 268
  · exact hroot.hOcc 274
  · exact hroot.hOcc 336
  · exact hroot.hOcc 350
  · exact hroot.hOcc 433
  · exact hroot.hOcc 436
  · exact hroot.hOcc 453
  · exact hroot.hOcc 503
  · exact hroot.hOcc 533
  · exact hroot.hOcc 542
  · exact hroot.hOcc 571
  · exact hroot.hOcc 572
  · exact hroot.hOcc 614
  · exact hroot.hOcc 623
  · exact hroot.hOcc 661
  · exact hroot.hOcc 666
  · exact hroot.hOcc 673
  · exact hroot.hOcc 697
  · exact hroot.hOcc 700
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5

end QiushiMatmul
