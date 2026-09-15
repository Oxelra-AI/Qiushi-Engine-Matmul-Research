import QiushiPlane487GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane487GenLeaf0048Refs : Fin 49 → RowRef 668 48 := ![.occ 87, .occ 89, .occ 94, .occ 100, .occ 103, .occ 104, .occ 111, .occ 122, .occ 162, .occ 189, .occ 191, .occ 231, .occ 235, .occ 246, .occ 260, .occ 288, .occ 341, .occ 343, .occ 347, .occ 381, .occ 414, .occ 470, .occ 497, .occ 536, .occ 575, .occ 586, .occ 608, .occ 621, .occ 649, .occ 650, .occ 656, .occ 661, .occ 666, .sumGe, .nonneg 8, .branchGe 39 (1), .branchLe 7 (0), .branchLe 28 (0), .branchLe 40 (0), .branchLe 29 (0), .branchLe 19 (0), .branchLe 36 (0), .branchLe 23 (0), .branchLe 45 (0), .branchLe 5 (0), .branchLe 25 (0), .branchLe 30 (0), .branchGe 2 (1), .branchLe 21 (0)]

def plane487GenLeaf0048Mult : Fin 49 → Nat := ![731, 15513, 10339, 2804, 4551, 10825, 6942, 8801, 9401, 252, 3287, 966, 2276, 7871, 8221, 136, 3444, 3396, 5837, 3054, 1809, 808, 4239, 403, 1598, 2568, 3377, 2877, 15, 13061, 755, 365, 1155, 23260, 3912, 17049, 14254, 15485, 23260, 23245, 23124, 5995, 19092, 23245, 22505, 16900, 7154, 15464, 21737]

theorem plane487GenLeaf0048 (x : Fin 48 → Int)
    (hroot : plane487GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_45 : x 45 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane487GenLeaf0048Refs i).resolveCoeff plane487GenOccSys j)
    (fun i => (plane487GenLeaf0048Refs i).resolveRhs plane487GenOccSys) plane487GenLeaf0048Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane487GenLeaf0048Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 89
  · exact hroot.hOcc 94
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 111
  · exact hroot.hOcc 122
  · exact hroot.hOcc 162
  · exact hroot.hOcc 189
  · exact hroot.hOcc 191
  · exact hroot.hOcc 231
  · exact hroot.hOcc 235
  · exact hroot.hOcc 246
  · exact hroot.hOcc 260
  · exact hroot.hOcc 288
  · exact hroot.hOcc 341
  · exact hroot.hOcc 343
  · exact hroot.hOcc 347
  · exact hroot.hOcc 381
  · exact hroot.hOcc 414
  · exact hroot.hOcc 470
  · exact hroot.hOcc 497
  · exact hroot.hOcc 536
  · exact hroot.hOcc 575
  · exact hroot.hOcc 586
  · exact hroot.hOcc 608
  · exact hroot.hOcc 621
  · exact hroot.hOcc 649
  · exact hroot.hOcc 650
  · exact hroot.hOcc 656
  · exact hroot.hOcc 661
  · exact hroot.hOcc 666
  · change (∑ j, (-1 : Int) * x j) ≤ -plane487GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 48) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (39 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (7 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (28 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (40 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (29 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (36 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (23 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (45 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_45
  · change (∑ k, (if k = (5 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (25 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (30 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (2 : Fin 48) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (21 : Fin 48) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21

end QiushiMatmul
