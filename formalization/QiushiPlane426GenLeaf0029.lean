import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0029Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 8, .occ 32, .occ 35, .occ 36, .occ 37, .occ 38, .occ 54, .occ 63, .occ 81, .occ 86, .occ 103, .occ 107, .occ 109, .occ 110, .occ 116, .occ 117, .occ 121, .occ 122, .occ 128, .occ 130, .occ 131, .occ 142, .occ 144, .occ 176, .occ 205, .occ 206, .occ 227, .occ 235, .occ 239, .occ 252, .occ 275, .occ 277, .occ 280, .occ 294, .occ 299, .occ 321, .occ 323, .occ 325, .occ 330, .occ 334, .sumGe, .nonneg 5, .nonneg 6, .nonneg 16, .nonneg 17, .nonneg 26, .nonneg 28, .nonneg 30, .nonneg 33, .nonneg 36, .nonneg 39, .nonneg 50, .branchLe 43 (0), .branchGe 14 (1), .branchLe 42 (0), .branchGe 18 (1), .branchGe 49 (1), .branchLe 0 (1)]

def plane426GenLeaf0029Mult : Fin 59 → Nat := ![2397, 4890, 667, 1855, 1581, 164, 1112, 409, 330, 1049, 3515, 974, 1178, 3253, 455, 1211, 1232, 931, 2065, 1664, 208, 1081, 1423, 1302, 766, 311, 865, 451, 491, 274, 1285, 705, 1112, 797, 196, 983, 463, 59, 2213, 131, 185, 5597, 5521, 594, 3563, 3888, 4958, 1611, 536, 984, 1150, 278, 943, 3687, 6220, 1039, 10069, 12508, 4498]

theorem plane426GenLeaf0029 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_49 : (1 : Int) ≤ x 49)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_0 : x 0 ≤ (1 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0029Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0029Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0029Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0029Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 8
  · exact hroot.hOcc 32
  · exact hroot.hOcc 35
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 54
  · exact hroot.hOcc 63
  · exact hroot.hOcc 81
  · exact hroot.hOcc 86
  · exact hroot.hOcc 103
  · exact hroot.hOcc 107
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 176
  · exact hroot.hOcc 205
  · exact hroot.hOcc 206
  · exact hroot.hOcc 227
  · exact hroot.hOcc 235
  · exact hroot.hOcc 239
  · exact hroot.hOcc 252
  · exact hroot.hOcc 275
  · exact hroot.hOcc 277
  · exact hroot.hOcc 280
  · exact hroot.hOcc 294
  · exact hroot.hOcc 299
  · exact hroot.hOcc 321
  · exact hroot.hOcc 323
  · exact hroot.hOcc 325
  · exact hroot.hOcc 330
  · exact hroot.hOcc 334
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (6 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (30 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (39 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (42 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (18 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (49 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_49
  · change (∑ k, (if k = (0 : Fin 58) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
