import QiushiPlane463GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane463GenLeaf0006Refs : Fin 64 → RowRef 278 63 := ![.occ 0, .occ 4, .occ 8, .occ 9, .occ 12, .occ 16, .occ 23, .occ 25, .occ 34, .occ 38, .occ 43, .occ 49, .occ 64, .occ 68, .occ 79, .occ 81, .occ 100, .occ 108, .occ 110, .occ 113, .occ 122, .occ 148, .occ 154, .occ 167, .occ 173, .occ 175, .occ 186, .occ 198, .occ 206, .occ 208, .occ 217, .occ 218, .occ 226, .occ 236, .occ 244, .occ 249, .occ 257, .occ 258, .occ 264, .occ 266, .occ 267, .occ 268, .occ 271, .occ 273, .occ 275, .occ 276, .sumGe, .nonneg 0, .nonneg 10, .nonneg 11, .nonneg 37, .nonneg 41, .nonneg 44, .nonneg 48, .nonneg 50, .nonneg 52, .nonneg 56, .nonneg 57, .nonneg 61, .branchLe 15 (0), .branchLe 24 (0), .branchLe 60 (0), .branchLe 21 (0), .branchGe 19 (1)]

def plane463GenLeaf0006Mult : Fin 64 → Nat := ![4984, 18140, 4784, 1520, 19160, 6264, 108, 516, 1456, 32048, 1724, 12008, 12952, 23472, 18052, 3424, 23616, 1304, 3428, 8332, 14656, 4632, 16856, 82, 16734, 1768, 3590, 4612, 230, 718, 2396, 2832, 616, 12874, 5420, 1448, 2614, 2270, 7405, 1832, 5005, 5530, 4224, 10247, 2021, 2508, 43384, 44048, 26732, 26292, 1876, 3516, 24300, 16448, 10980, 6068, 24628, 12120, 28768, 28096, 13580, 5848, 28704, 161600]

theorem plane463GenLeaf0006 (x : Fin 63 → Int)
    (hroot : plane463GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane463GenLeaf0006Refs i).resolveCoeff plane463GenOccSys j)
    (fun i => (plane463GenLeaf0006Refs i).resolveRhs plane463GenOccSys) plane463GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane463GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 4
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 12
  · exact hroot.hOcc 16
  · exact hroot.hOcc 23
  · exact hroot.hOcc 25
  · exact hroot.hOcc 34
  · exact hroot.hOcc 38
  · exact hroot.hOcc 43
  · exact hroot.hOcc 49
  · exact hroot.hOcc 64
  · exact hroot.hOcc 68
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 100
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 113
  · exact hroot.hOcc 122
  · exact hroot.hOcc 148
  · exact hroot.hOcc 154
  · exact hroot.hOcc 167
  · exact hroot.hOcc 173
  · exact hroot.hOcc 175
  · exact hroot.hOcc 186
  · exact hroot.hOcc 198
  · exact hroot.hOcc 206
  · exact hroot.hOcc 208
  · exact hroot.hOcc 217
  · exact hroot.hOcc 218
  · exact hroot.hOcc 226
  · exact hroot.hOcc 236
  · exact hroot.hOcc 244
  · exact hroot.hOcc 249
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 264
  · exact hroot.hOcc 266
  · exact hroot.hOcc 267
  · exact hroot.hOcc 268
  · exact hroot.hOcc 271
  · exact hroot.hOcc 273
  · exact hroot.hOcc 275
  · exact hroot.hOcc 276
  · change (∑ j, (-1 : Int) * x j) ≤ -plane463GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (41 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (50 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (56 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (57 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (15 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (60 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (21 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (19 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19

end QiushiMatmul
