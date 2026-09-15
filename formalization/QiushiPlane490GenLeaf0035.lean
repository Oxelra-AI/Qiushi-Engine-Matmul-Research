import QiushiPlane490GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane490GenLeaf0035Refs : Fin 44 → RowRef 713 43 := ![.occ 90, .occ 94, .occ 95, .occ 99, .occ 106, .occ 107, .occ 109, .occ 110, .occ 113, .occ 139, .occ 140, .occ 145, .occ 216, .occ 219, .occ 258, .occ 270, .occ 272, .occ 290, .occ 300, .occ 302, .occ 303, .occ 336, .occ 379, .occ 503, .occ 506, .occ 540, .occ 575, .occ 599, .occ 601, .occ 664, .occ 666, .occ 667, .occ 679, .occ 694, .sumGe, .branchLe 29 (0), .branchLe 4 (0), .branchGe 23 (1), .branchLe 30 (0), .branchLe 28 (0), .branchLe 35 (0), .branchLe 5 (0), .branchLe 38 (0), .branchGe 25 (1)]

def plane490GenLeaf0035Mult : Fin 44 → Nat := ![526, 1014, 939, 1545, 20, 1902, 1137, 401, 1128, 205, 1012, 433, 491, 67, 1069, 115, 15, 101, 1497, 833, 476, 800, 634, 620, 421, 233, 142, 61, 280, 587, 192, 624, 486, 253, 2378, 2378, 2277, 2680, 1325, 2378, 2186, 2125, 1312, 9287]

theorem plane490GenLeaf0035 (x : Fin 43 → Int)
    (hroot : plane490GenOccSys.RootHolds x)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane490GenLeaf0035Refs i).resolveCoeff plane490GenOccSys j)
    (fun i => (plane490GenLeaf0035Refs i).resolveRhs plane490GenOccSys) plane490GenLeaf0035Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane490GenLeaf0035Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 90
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 145
  · exact hroot.hOcc 216
  · exact hroot.hOcc 219
  · exact hroot.hOcc 258
  · exact hroot.hOcc 270
  · exact hroot.hOcc 272
  · exact hroot.hOcc 290
  · exact hroot.hOcc 300
  · exact hroot.hOcc 302
  · exact hroot.hOcc 303
  · exact hroot.hOcc 336
  · exact hroot.hOcc 379
  · exact hroot.hOcc 503
  · exact hroot.hOcc 506
  · exact hroot.hOcc 540
  · exact hroot.hOcc 575
  · exact hroot.hOcc 599
  · exact hroot.hOcc 601
  · exact hroot.hOcc 664
  · exact hroot.hOcc 666
  · exact hroot.hOcc 667
  · exact hroot.hOcc 679
  · exact hroot.hOcc 694
  · change (∑ j, (-1 : Int) * x j) ≤ -plane490GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
