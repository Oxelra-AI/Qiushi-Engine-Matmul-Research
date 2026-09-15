import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0082Refs : Fin 44 → RowRef 713 43 := ![.occ 85, .occ 86, .occ 89, .occ 94, .occ 95, .occ 105, .occ 108, .occ 112, .occ 178, .occ 183, .occ 191, .occ 202, .occ 231, .occ 247, .occ 250, .occ 290, .occ 317, .occ 373, .occ 375, .occ 397, .occ 441, .occ 466, .occ 474, .occ 486, .occ 505, .occ 521, .occ 542, .occ 595, .occ 596, .occ 602, .occ 653, .occ 664, .occ 700, .occ 701, .occ 704, .sumGe, .branchGe 29 (1), .branchLe 18 (0), .branchLe 12 (0), .branchLe 22 (0), .branchLe 42 (0), .branchLe 32 (0), .branchLe 8 (0), .branchGe 16 (1)]

def plane490GenLeaf0082Mult : Fin 44 → Nat := ![18625, 46330, 21698, 143286, 24097, 150678, 98686, 7642, 73759, 24945, 741, 40430, 31088, 4417, 17482, 4101, 155, 287, 42148, 51956, 19859, 4605, 1005, 39046, 56843, 19634, 34446, 10354, 47127, 63368, 4669, 25516, 2723, 11257, 5266, 150678, 388145, 87310, 96598, 143538, 116232, 140324, 134155, 335495]

theorem plane490GenLeaf0082 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0082Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0082Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0082Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0082Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 89
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 112
  · exact hroot.hOcc 178
  · exact hroot.hOcc 183
  · exact hroot.hOcc 191
  · exact hroot.hOcc 202
  · exact hroot.hOcc 231
  · exact hroot.hOcc 247
  · exact hroot.hOcc 250
  · exact hroot.hOcc 290
  · exact hroot.hOcc 317
  · exact hroot.hOcc 373
  · exact hroot.hOcc 375
  · exact hroot.hOcc 397
  · exact hroot.hOcc 441
  · exact hroot.hOcc 466
  · exact hroot.hOcc 474
  · exact hroot.hOcc 486
  · exact hroot.hOcc 505
  · exact hroot.hOcc 521
  · exact hroot.hOcc 542
  · exact hroot.hOcc 595
  · exact hroot.hOcc 596
  · exact hroot.hOcc 602
  · exact hroot.hOcc 653
  · exact hroot.hOcc 664
  · exact hroot.hOcc 700
  · exact hroot.hOcc 701
  · exact hroot.hOcc 704
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
