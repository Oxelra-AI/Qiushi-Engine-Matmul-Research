import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0083Refs : Fin 36 → RowRef 713 43 := ![.occ 89, .occ 90, .occ 91, .occ 94, .occ 102, .occ 107, .occ 108, .occ 115, .occ 174, .occ 225, .occ 250, .occ 258, .occ 294, .occ 311, .occ 420, .occ 458, .occ 472, .occ 544, .occ 590, .occ 602, .occ 632, .occ 646, .occ 653, .occ 688, .occ 701, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchLe 22 (0), .branchGe 1 (1), .branchLe 42 (0), .branchLe 32 (0), .branchGe 8 (1), .branchLe 23 (0), .branchLe 10 (0)]

def plane490GenLeaf0083Mult : Fin 36 → Nat := ![7, 5, 1, 8, 8, 4, 18, 10, 10, 4, 7, 6, 4, 12, 4, 1, 7, 8, 5, 4, 13, 1, 8, 6, 5, 25, 82, 21, 13, 6, 6, 21, 12, 41, 14, 12]

theorem plane490GenLeaf0083 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0083Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0083Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0083Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0083Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 102
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 115
  · exact hroot.hOcc 174
  · exact hroot.hOcc 225
  · exact hroot.hOcc 250
  · exact hroot.hOcc 258
  · exact hroot.hOcc 294
  · exact hroot.hOcc 311
  · exact hroot.hOcc 420
  · exact hroot.hOcc 458
  · exact hroot.hOcc 472
  · exact hroot.hOcc 544
  · exact hroot.hOcc 590
  · exact hroot.hOcc 602
  · exact hroot.hOcc 632
  · exact hroot.hOcc 646
  · exact hroot.hOcc 653
  · exact hroot.hOcc 688
  · exact hroot.hOcc 701
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
