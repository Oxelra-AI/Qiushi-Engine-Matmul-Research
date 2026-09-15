import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0000Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 32, .occ 35, .occ 56, .occ 76, .occ 86, .occ 104, .occ 107, .occ 113, .occ 122, .occ 124, .occ 126, .occ 142, .occ 144, .occ 147, .occ 151, .occ 160, .occ 190, .occ 194, .occ 196, .occ 197, .occ 201, .occ 206, .occ 208, .occ 249, .occ 260, .occ 262, .occ 276, .occ 278, .occ 279, .occ 280, .occ 281, .occ 282, .occ 292, .occ 321, .occ 322, .occ 326, .occ 327, .occ 328, .occ 329, .occ 331, .occ 334, .occ 335, .sumGe, .nonneg 5, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 22, .nonneg 28, .nonneg 32, .nonneg 40, .nonneg 52, .branchLe 43 (0), .branchLe 14 (0), .branchLe 1 (0), .branchLe 13 (0), .branchLe 37 (0), .branchLe 21 (0)]

def plane426GenLeaf0000Mult : Fin 59 → Nat := ![966256, 379952, 415936, 208624, 541596, 179216, 518804, 345752, 47096, 252888, 255856, 1602492, 903872, 810456, 358592, 89896, 74888, 242960, 263540, 280128, 385364, 16892, 203928, 305768, 353024, 60012, 111912, 112576, 334605, 7188, 39393, 463155, 483147, 259508, 529453, 750987, 22024, 15947, 137917, 1293491, 1395469, 1219392, 1422472, 4982704, 2877016, 6071384, 3489664, 2981176, 55696, 34256, 30128, 1349592, 1033704, 3082800, 4913584, 4803488, 1177568, 977488, 4649728]

theorem plane426GenLeaf0000 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0000Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0000Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 32
  · exact hroot.hOcc 35
  · exact hroot.hOcc 56
  · exact hroot.hOcc 76
  · exact hroot.hOcc 86
  · exact hroot.hOcc 104
  · exact hroot.hOcc 107
  · exact hroot.hOcc 113
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 147
  · exact hroot.hOcc 151
  · exact hroot.hOcc 160
  · exact hroot.hOcc 190
  · exact hroot.hOcc 194
  · exact hroot.hOcc 196
  · exact hroot.hOcc 197
  · exact hroot.hOcc 201
  · exact hroot.hOcc 206
  · exact hroot.hOcc 208
  · exact hroot.hOcc 249
  · exact hroot.hOcc 260
  · exact hroot.hOcc 262
  · exact hroot.hOcc 276
  · exact hroot.hOcc 278
  · exact hroot.hOcc 279
  · exact hroot.hOcc 280
  · exact hroot.hOcc 281
  · exact hroot.hOcc 282
  · exact hroot.hOcc 292
  · exact hroot.hOcc 321
  · exact hroot.hOcc 322
  · exact hroot.hOcc 326
  · exact hroot.hOcc 327
  · exact hroot.hOcc 328
  · exact hroot.hOcc 329
  · exact hroot.hOcc 331
  · exact hroot.hOcc 334
  · exact hroot.hOcc 335
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (22 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (32 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (40 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (52 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (13 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (21 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21

end QiushiMatmul
