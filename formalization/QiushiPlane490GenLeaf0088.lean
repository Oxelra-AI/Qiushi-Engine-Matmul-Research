import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0088Refs : Fin 44 → RowRef 713 43 := ![.occ 84, .occ 85, .occ 86, .occ 89, .occ 102, .occ 105, .occ 106, .occ 108, .occ 109, .occ 111, .occ 112, .occ 114, .occ 151, .occ 157, .occ 221, .occ 228, .occ 231, .occ 274, .occ 290, .occ 302, .occ 316, .occ 334, .occ 364, .occ 381, .occ 471, .occ 482, .occ 505, .occ 521, .occ 622, .occ 632, .occ 655, .occ 663, .occ 709, .occ 711, .occ 712, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchLe 22 (0), .branchLe 42 (0), .branchGe 32 (1), .branchLe 2 (0), .branchGe 34 (1)]

def plane490GenLeaf0088Mult : Fin 44 → Nat := ![11, 3, 1, 3, 36, 17, 25, 36, 2, 27, 12, 34, 3, 21, 13, 7, 6, 12, 5, 6, 5, 10, 6, 6, 2, 5, 2, 6, 9, 18, 2, 7, 3, 6, 17, 41, 95, 22, 14, 23, 30, 91, 34, 126]

theorem plane490GenLeaf0088 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0088Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0088Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0088Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0088Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 89
  · exact hroot.hOcc 102
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 151
  · exact hroot.hOcc 157
  · exact hroot.hOcc 221
  · exact hroot.hOcc 228
  · exact hroot.hOcc 231
  · exact hroot.hOcc 274
  · exact hroot.hOcc 290
  · exact hroot.hOcc 302
  · exact hroot.hOcc 316
  · exact hroot.hOcc 334
  · exact hroot.hOcc 364
  · exact hroot.hOcc 381
  · exact hroot.hOcc 471
  · exact hroot.hOcc 482
  · exact hroot.hOcc 505
  · exact hroot.hOcc 521
  · exact hroot.hOcc 622
  · exact hroot.hOcc 632
  · exact hroot.hOcc 655
  · exact hroot.hOcc 663
  · exact hroot.hOcc 709
  · exact hroot.hOcc 711
  · exact hroot.hOcc 712
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34

end QiushiMatmul
