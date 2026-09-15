import QiushiPlane463GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane463GenLeaf0000Refs : Fin 64 → RowRef 278 63 := ![.occ 8, .occ 16, .occ 19, .occ 21, .occ 22, .occ 27, .occ 39, .occ 40, .occ 53, .occ 61, .occ 63, .occ 74, .occ 77, .occ 79, .occ 95, .occ 98, .occ 99, .occ 109, .occ 110, .occ 114, .occ 116, .occ 118, .occ 120, .occ 131, .occ 153, .occ 154, .occ 163, .occ 166, .occ 168, .occ 169, .occ 170, .occ 173, .occ 175, .occ 180, .occ 187, .occ 200, .occ 217, .occ 218, .occ 220, .occ 222, .occ 232, .occ 236, .occ 259, .occ 264, .occ 266, .occ 268, .occ 275, .occ 276, .sumGe, .nonneg 0, .nonneg 10, .nonneg 13, .nonneg 54, .nonneg 61, .branchLe 15 (0), .branchLe 24 (0), .branchLe 60 (0), .branchLe 21 (0), .branchLe 19 (0), .branchLe 47 (0), .branchLe 22 (0), .branchLe 20 (0), .branchLe 2 (0), .branchLe 29 (0)]

def plane463GenLeaf0000Mult : Fin 64 → Nat := ![1173854, 591646, 1014042, 619958, 507842, 1502748, 1870363, 6790, 2199191, 660954, 117170, 1440414, 1611832, 1572510, 740440, 1635170, 1283977, 2357818, 1744764, 1017456, 628288, 1600205, 1435413, 72563, 1935509, 1507023, 63246, 1006533, 2072731, 647747, 406412, 594101, 1396766, 396863, 1331109, 1401795, 315806, 705274, 900068, 1756850, 142789, 940000, 2094874, 73581, 230440, 594885, 652393, 287362, 7917575, 8484765, 3074296, 2129411, 2822681, 2228127, 6330073, 6486327, 7399773, 5794452, 1952534, 7314407, 4424851, 3566569, 5984122, 6032082]

theorem plane463GenLeaf0000 (x : Fin 63 → Int)
    (hroot : plane463GenOccSys.RootHolds x)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_47 : x 47 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane463GenLeaf0000Refs i).resolveCoeff plane463GenOccSys j)
    (fun i => (plane463GenLeaf0000Refs i).resolveRhs plane463GenOccSys) plane463GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane463GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 16
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 27
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 53
  · exact hroot.hOcc 61
  · exact hroot.hOcc 63
  · exact hroot.hOcc 74
  · exact hroot.hOcc 77
  · exact hroot.hOcc 79
  · exact hroot.hOcc 95
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 120
  · exact hroot.hOcc 131
  · exact hroot.hOcc 153
  · exact hroot.hOcc 154
  · exact hroot.hOcc 163
  · exact hroot.hOcc 166
  · exact hroot.hOcc 168
  · exact hroot.hOcc 169
  · exact hroot.hOcc 170
  · exact hroot.hOcc 173
  · exact hroot.hOcc 175
  · exact hroot.hOcc 180
  · exact hroot.hOcc 187
  · exact hroot.hOcc 200
  · exact hroot.hOcc 217
  · exact hroot.hOcc 218
  · exact hroot.hOcc 220
  · exact hroot.hOcc 222
  · exact hroot.hOcc 232
  · exact hroot.hOcc 236
  · exact hroot.hOcc 259
  · exact hroot.hOcc 264
  · exact hroot.hOcc 266
  · exact hroot.hOcc 268
  · exact hroot.hOcc 275
  · exact hroot.hOcc 276
  · change (∑ j, (-1 : Int) * x j) ≤ -plane463GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (13 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (54 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (15 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (60 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (21 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (19 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (47 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_47
  · change (∑ k, (if k = (22 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (20 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (2 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29

end QiushiMatmul
