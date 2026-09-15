import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0046Refs : Fin 49 → RowRef 726 49 := ![.occ 97, .occ 99, .occ 108, .occ 114, .occ 119, .occ 122, .occ 166, .occ 172, .occ 192, .occ 241, .occ 243, .occ 257, .occ 262, .occ 292, .occ 304, .occ 325, .occ 332, .occ 351, .occ 363, .occ 364, .occ 372, .occ 375, .occ 401, .occ 423, .occ 431, .occ 460, .occ 494, .occ 500, .occ 515, .occ 526, .occ 542, .occ 552, .occ 554, .occ 571, .occ 594, .occ 602, .occ 640, .occ 649, .occ 719, .sumGe, .nonneg 8, .nonneg 22, .nonneg 46, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchGe 29 (1), .branchGe 43 (1), .branchGe 32 (1)]

def plane491GenLeaf0046Mult : Fin 49 → Nat := ![5685, 22053, 11493, 16122, 5473, 2268, 4677, 1608, 6528, 1130, 10665, 1945, 1730, 8147, 3131, 11130, 5111, 6216, 2679, 5473, 5815, 211, 24823, 6020, 4856, 3063, 2460, 9631, 2770, 2582, 1723, 585, 5065, 2244, 8216, 3545, 1219, 3857, 286, 24823, 11354, 4856, 2582, 17298, 15881, 21858, 56775, 90603, 86695]

theorem plane491GenLeaf0046 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0046Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0046Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0046Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0046Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 97
  · exact hroot.hOcc 99
  · exact hroot.hOcc 108
  · exact hroot.hOcc 114
  · exact hroot.hOcc 119
  · exact hroot.hOcc 122
  · exact hroot.hOcc 166
  · exact hroot.hOcc 172
  · exact hroot.hOcc 192
  · exact hroot.hOcc 241
  · exact hroot.hOcc 243
  · exact hroot.hOcc 257
  · exact hroot.hOcc 262
  · exact hroot.hOcc 292
  · exact hroot.hOcc 304
  · exact hroot.hOcc 325
  · exact hroot.hOcc 332
  · exact hroot.hOcc 351
  · exact hroot.hOcc 363
  · exact hroot.hOcc 364
  · exact hroot.hOcc 372
  · exact hroot.hOcc 375
  · exact hroot.hOcc 401
  · exact hroot.hOcc 423
  · exact hroot.hOcc 431
  · exact hroot.hOcc 460
  · exact hroot.hOcc 494
  · exact hroot.hOcc 500
  · exact hroot.hOcc 515
  · exact hroot.hOcc 526
  · exact hroot.hOcc 542
  · exact hroot.hOcc 552
  · exact hroot.hOcc 554
  · exact hroot.hOcc 571
  · exact hroot.hOcc 594
  · exact hroot.hOcc 602
  · exact hroot.hOcc 640
  · exact hroot.hOcc 649
  · exact hroot.hOcc 719
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (22 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (46 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32

end QiushiMatmul
