import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0040Refs : Fin 44 → RowRef 713 43 := ![.occ 89, .occ 93, .occ 95, .occ 102, .occ 106, .occ 110, .occ 134, .occ 135, .occ 137, .occ 198, .occ 205, .occ 219, .occ 238, .occ 259, .occ 260, .occ 268, .occ 279, .occ 283, .occ 284, .occ 295, .occ 296, .occ 302, .occ 303, .occ 318, .occ 375, .occ 391, .occ 485, .occ 499, .occ 575, .occ 599, .occ 617, .occ 618, .occ 668, .occ 692, .occ 704, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchLe 35 (0), .branchGe 5 (1), .branchGe 19 (1)]

def plane490GenLeaf0040Mult : Fin 44 → Nat := ![180, 151, 193, 944, 287, 1439, 575, 98, 327, 224, 537, 248, 612, 113, 193, 308, 898, 12, 421, 255, 334, 674, 160, 374, 428, 1012, 342, 344, 462, 193, 158, 669, 449, 191, 301, 1933, 1933, 1344, 2456, 1933, 1314, 662, 4793, 4531]

theorem plane490GenLeaf0040 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0040Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0040Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0040Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0040Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 89
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 110
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 198
  · exact hroot.hOcc 205
  · exact hroot.hOcc 219
  · exact hroot.hOcc 238
  · exact hroot.hOcc 259
  · exact hroot.hOcc 260
  · exact hroot.hOcc 268
  · exact hroot.hOcc 279
  · exact hroot.hOcc 283
  · exact hroot.hOcc 284
  · exact hroot.hOcc 295
  · exact hroot.hOcc 296
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 318
  · exact hroot.hOcc 375
  · exact hroot.hOcc 391
  · exact hroot.hOcc 485
  · exact hroot.hOcc 499
  · exact hroot.hOcc 575
  · exact hroot.hOcc 599
  · exact hroot.hOcc 617
  · exact hroot.hOcc 618
  · exact hroot.hOcc 668
  · exact hroot.hOcc 692
  · exact hroot.hOcc 704
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19

end QiushiMatmul
