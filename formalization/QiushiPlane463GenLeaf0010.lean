import QiushiPlane463GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane463GenLeaf0010Refs : Fin 63 → RowRef 278 63 := ![.occ 2, .occ 3, .occ 13, .occ 14, .occ 30, .occ 33, .occ 39, .occ 47, .occ 73, .occ 79, .occ 91, .occ 98, .occ 104, .occ 107, .occ 109, .occ 110, .occ 114, .occ 131, .occ 137, .occ 144, .occ 164, .occ 165, .occ 172, .occ 173, .occ 176, .occ 197, .occ 202, .occ 218, .occ 222, .occ 226, .occ 229, .occ 236, .occ 244, .occ 259, .occ 260, .occ 264, .occ 265, .occ 266, .occ 267, .occ 268, .occ 270, .occ 273, .occ 275, .sumGe, .nonneg 0, .nonneg 10, .nonneg 11, .nonneg 14, .nonneg 37, .nonneg 38, .nonneg 40, .nonneg 42, .nonneg 43, .nonneg 44, .nonneg 48, .nonneg 49, .nonneg 52, .nonneg 54, .nonneg 57, .nonneg 59, .nonneg 61, .branchLe 15 (0), .branchGe 24 (1)]

def plane463GenLeaf0010Mult : Fin 63 → Nat := ![1976988, 3081050, 259376, 667704, 3548028, 809932, 460520, 151264, 2442676, 1821852, 1704890, 357972, 602342, 1111800, 254624, 672476, 560392, 765480, 3224390, 31264, 77694, 620322, 1172030, 425526, 1204342, 560076, 413614, 1875756, 7154, 274854, 479592, 293042, 313442, 75506, 55348, 302104, 132597, 443403, 853342, 473747, 217007, 1488454, 210674, 4586100, 2675796, 2637444, 831972, 860588, 1782924, 881972, 932672, 1727472, 161234, 68120, 144644, 2664108, 1673598, 1102532, 112064, 1416216, 394464, 3522084, 23024606]

theorem plane463GenLeaf0010 (x : Fin 63 → Int)
    (hroot : plane463GenOccSys.RootHolds x)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_15 : x 15 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane463GenLeaf0010Refs i).resolveCoeff plane463GenOccSys j)
    (fun i => (plane463GenLeaf0010Refs i).resolveRhs plane463GenOccSys) plane463GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane463GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 3
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 30
  · exact hroot.hOcc 33
  · exact hroot.hOcc 39
  · exact hroot.hOcc 47
  · exact hroot.hOcc 73
  · exact hroot.hOcc 79
  · exact hroot.hOcc 91
  · exact hroot.hOcc 98
  · exact hroot.hOcc 104
  · exact hroot.hOcc 107
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 114
  · exact hroot.hOcc 131
  · exact hroot.hOcc 137
  · exact hroot.hOcc 144
  · exact hroot.hOcc 164
  · exact hroot.hOcc 165
  · exact hroot.hOcc 172
  · exact hroot.hOcc 173
  · exact hroot.hOcc 176
  · exact hroot.hOcc 197
  · exact hroot.hOcc 202
  · exact hroot.hOcc 218
  · exact hroot.hOcc 222
  · exact hroot.hOcc 226
  · exact hroot.hOcc 229
  · exact hroot.hOcc 236
  · exact hroot.hOcc 244
  · exact hroot.hOcc 259
  · exact hroot.hOcc 260
  · exact hroot.hOcc 264
  · exact hroot.hOcc 265
  · exact hroot.hOcc 266
  · exact hroot.hOcc 267
  · exact hroot.hOcc 268
  · exact hroot.hOcc 270
  · exact hroot.hOcc 273
  · exact hroot.hOcc 275
  · change (∑ j, (-1 : Int) * x j) ≤ -plane463GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (14 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (40 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (43 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (54 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (57 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (15 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (24 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
