import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0084Refs : Fin 39 → RowRef 713 43 := ![.occ 93, .occ 105, .occ 107, .occ 108, .occ 115, .occ 117, .occ 123, .occ 127, .occ 148, .occ 152, .occ 178, .occ 180, .occ 195, .occ 196, .occ 198, .occ 202, .occ 233, .occ 248, .occ 250, .occ 257, .occ 258, .occ 364, .occ 375, .occ 429, .occ 505, .occ 549, .occ 636, .occ 701, .occ 710, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchLe 22 (0), .branchGe 1 (1), .branchLe 42 (0), .branchLe 32 (0), .branchGe 8 (1), .branchLe 23 (0), .branchGe 10 (1)]

def plane490GenLeaf0084Mult : Fin 39 → Nat := ![4, 30, 13, 28, 4, 6, 6, 14, 6, 26, 9, 7, 6, 4, 16, 18, 4, 2, 4, 14, 10, 12, 8, 1, 13, 6, 5, 7, 6, 32, 93, 32, 26, 16, 20, 32, 24, 32, 103]

theorem plane490GenLeaf0084 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0084Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0084Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0084Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0084Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 93
  · exact hroot.hOcc 105
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 115
  · exact hroot.hOcc 117
  · exact hroot.hOcc 123
  · exact hroot.hOcc 127
  · exact hroot.hOcc 148
  · exact hroot.hOcc 152
  · exact hroot.hOcc 178
  · exact hroot.hOcc 180
  · exact hroot.hOcc 195
  · exact hroot.hOcc 196
  · exact hroot.hOcc 198
  · exact hroot.hOcc 202
  · exact hroot.hOcc 233
  · exact hroot.hOcc 248
  · exact hroot.hOcc 250
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 364
  · exact hroot.hOcc 375
  · exact hroot.hOcc 429
  · exact hroot.hOcc 505
  · exact hroot.hOcc 549
  · exact hroot.hOcc 636
  · exact hroot.hOcc 701
  · exact hroot.hOcc 710
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
