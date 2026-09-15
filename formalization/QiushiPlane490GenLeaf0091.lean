import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0091Refs : Fin 44 → RowRef 713 43 := ![.occ 91, .occ 94, .occ 97, .occ 99, .occ 105, .occ 108, .occ 113, .occ 129, .occ 139, .occ 161, .occ 170, .occ 186, .occ 202, .occ 213, .occ 232, .occ 239, .occ 247, .occ 248, .occ 252, .occ 295, .occ 302, .occ 323, .occ 336, .occ 350, .occ 362, .occ 454, .occ 494, .occ 503, .occ 509, .occ 545, .occ 625, .occ 632, .occ 652, .occ 653, .occ 667, .occ 701, .occ 708, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchGe 22 (1), .branchLe 3 (0), .branchLe 2 (0)]

def plane490GenLeaf0091Mult : Fin 44 → Nat := ![998, 1051, 2411, 342, 8111, 3936, 4198, 3048, 259, 3285, 5790, 628, 1244, 1708, 36, 2847, 110, 1011, 4580, 4734, 807, 1561, 231, 228, 2962, 687, 2221, 228, 562, 1239, 190, 1019, 44, 2562, 3367, 459, 2690, 9122, 19400, 3939, 5286, 31587, 8103, 8663]

theorem plane490GenLeaf0091 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0091Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0091Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0091Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0091Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 97
  · exact hroot.hOcc 99
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 113
  · exact hroot.hOcc 129
  · exact hroot.hOcc 139
  · exact hroot.hOcc 161
  · exact hroot.hOcc 170
  · exact hroot.hOcc 186
  · exact hroot.hOcc 202
  · exact hroot.hOcc 213
  · exact hroot.hOcc 232
  · exact hroot.hOcc 239
  · exact hroot.hOcc 247
  · exact hroot.hOcc 248
  · exact hroot.hOcc 252
  · exact hroot.hOcc 295
  · exact hroot.hOcc 302
  · exact hroot.hOcc 323
  · exact hroot.hOcc 336
  · exact hroot.hOcc 350
  · exact hroot.hOcc 362
  · exact hroot.hOcc 454
  · exact hroot.hOcc 494
  · exact hroot.hOcc 503
  · exact hroot.hOcc 509
  · exact hroot.hOcc 545
  · exact hroot.hOcc 625
  · exact hroot.hOcc 632
  · exact hroot.hOcc 652
  · exact hroot.hOcc 653
  · exact hroot.hOcc 667
  · exact hroot.hOcc 701
  · exact hroot.hOcc 708
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2

end QiushiMatmul
