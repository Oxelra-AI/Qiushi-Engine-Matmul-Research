import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0014Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 8, .occ 11, .occ 13, .occ 40, .occ 51, .occ 69, .occ 71, .occ 74, .occ 81, .occ 88, .occ 89, .occ 104, .occ 113, .occ 124, .occ 126, .occ 127, .occ 132, .occ 134, .occ 138, .occ 142, .occ 195, .occ 199, .occ 200, .occ 213, .occ 222, .occ 226, .occ 235, .occ 238, .occ 278, .occ 282, .occ 285, .occ 306, .occ 321, .occ 323, .occ 333, .occ 334, .occ 335, .sumGe, .nonneg 6, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 22, .nonneg 23, .nonneg 26, .nonneg 32, .nonneg 36, .nonneg 40, .nonneg 42, .nonneg 47, .nonneg 50, .nonneg 54, .branchLe 43 (0), .branchLe 14 (0), .branchGe 1 (1), .branchLe 35 (0), .branchGe 4 (1), .branchGe 29 (1)]

def plane426GenLeaf0014Mult : Fin 59 → Nat := ![2668, 5579, 2481, 1035, 2287, 5638, 715, 1448, 464, 1762, 5043, 286, 447, 4417, 3186, 1918, 1033, 1070, 1618, 2689, 5823, 673, 2638, 510, 1300, 3719, 412, 2152, 847, 809, 1566, 624, 721, 451, 1183, 1156, 88, 685, 8103, 1545, 8654, 8644, 4778, 3962, 2036, 5300, 1917, 2541, 767, 641, 582, 3006, 1010, 2744, 1924, 4183, 1510, 18224, 26467]

theorem plane426GenLeaf0014 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0014Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0014Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0014Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0014Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 8
  · exact hroot.hOcc 11
  · exact hroot.hOcc 13
  · exact hroot.hOcc 40
  · exact hroot.hOcc 51
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 74
  · exact hroot.hOcc 81
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 104
  · exact hroot.hOcc 113
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 195
  · exact hroot.hOcc 199
  · exact hroot.hOcc 200
  · exact hroot.hOcc 213
  · exact hroot.hOcc 222
  · exact hroot.hOcc 226
  · exact hroot.hOcc 235
  · exact hroot.hOcc 238
  · exact hroot.hOcc 278
  · exact hroot.hOcc 282
  · exact hroot.hOcc 285
  · exact hroot.hOcc 306
  · exact hroot.hOcc 321
  · exact hroot.hOcc 323
  · exact hroot.hOcc 333
  · exact hroot.hOcc 334
  · exact hroot.hOcc 335
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (22 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (32 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (40 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (42 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (54 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (35 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (4 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (29 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29

end QiushiMatmul
