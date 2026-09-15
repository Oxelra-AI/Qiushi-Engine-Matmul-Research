import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0026Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 8, .occ 21, .occ 24, .occ 47, .occ 61, .occ 65, .occ 76, .occ 79, .occ 81, .occ 86, .occ 91, .occ 96, .occ 103, .occ 104, .occ 109, .occ 114, .occ 117, .occ 121, .occ 122, .occ 124, .occ 131, .occ 144, .occ 180, .occ 205, .occ 219, .occ 225, .occ 227, .occ 235, .occ 258, .occ 282, .occ 297, .occ 299, .occ 316, .occ 317, .occ 325, .occ 335, .sumGe, .nonneg 5, .nonneg 8, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 23, .nonneg 25, .nonneg 26, .nonneg 28, .nonneg 36, .nonneg 40, .nonneg 47, .nonneg 49, .nonneg 50, .nonneg 54, .branchLe 43 (0), .branchGe 14 (1), .branchLe 42 (0), .branchGe 18 (1), .branchLe 27 (0), .branchGe 35 (1)]

def plane426GenLeaf0026Mult : Fin 59 → Nat := ![699, 3910, 845, 1508, 966, 933, 3016, 1753, 81, 431, 2907, 1561, 256, 758, 719, 2150, 1650, 513, 1435, 1393, 178, 1663, 322, 458, 184, 682, 243, 1014, 1090, 2329, 1270, 393, 89, 280, 704, 1526, 24, 4457, 2494, 203, 6205, 3917, 707, 944, 830, 2750, 3822, 1036, 1858, 1989, 309, 2525, 2239, 4088, 5964, 1756, 10640, 4433, 10619]

theorem plane426GenLeaf0026 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_49 : x 49 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0026Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0026Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0026Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0026Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 8
  · exact hroot.hOcc 21
  · exact hroot.hOcc 24
  · exact hroot.hOcc 47
  · exact hroot.hOcc 61
  · exact hroot.hOcc 65
  · exact hroot.hOcc 76
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 86
  · exact hroot.hOcc 91
  · exact hroot.hOcc 96
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 109
  · exact hroot.hOcc 114
  · exact hroot.hOcc 117
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 131
  · exact hroot.hOcc 144
  · exact hroot.hOcc 180
  · exact hroot.hOcc 205
  · exact hroot.hOcc 219
  · exact hroot.hOcc 225
  · exact hroot.hOcc 227
  · exact hroot.hOcc 235
  · exact hroot.hOcc 258
  · exact hroot.hOcc 282
  · exact hroot.hOcc 297
  · exact hroot.hOcc 299
  · exact hroot.hOcc 316
  · exact hroot.hOcc 317
  · exact hroot.hOcc 325
  · exact hroot.hOcc 335
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (8 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (40 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (49 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (54 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (42 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (18 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (27 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (35 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
