import QiushiPlane468GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane468GenLeaf0000Refs : Fin 63 → RowRef 253 62 := ![.occ 2, .occ 5, .occ 6, .occ 8, .occ 9, .occ 10, .occ 29, .occ 35, .occ 53, .occ 66, .occ 69, .occ 80, .occ 81, .occ 97, .occ 103, .occ 105, .occ 108, .occ 109, .occ 113, .occ 116, .occ 118, .occ 121, .occ 127, .occ 135, .occ 136, .occ 137, .occ 142, .occ 158, .occ 162, .occ 167, .occ 169, .occ 173, .occ 195, .occ 202, .occ 207, .occ 209, .occ 213, .occ 215, .occ 219, .occ 229, .occ 232, .occ 238, .occ 239, .occ 242, .occ 245, .occ 247, .occ 248, .occ 249, .sumGe, .nonneg 3, .nonneg 8, .nonneg 10, .nonneg 20, .nonneg 39, .nonneg 45, .nonneg 50, .nonneg 54, .nonneg 56, .nonneg 59, .nonneg 60, .branchLe 28 (0), .branchLe 51 (0), .branchLe 47 (0)]

def plane468GenLeaf0000Mult : Fin 63 → Nat := ![157194, 1380937, 15607, 188228, 1472762, 501173, 1002573, 508144, 849584, 5304779, 536552, 194719, 505242, 189147, 2892519, 463070, 1265468, 539330, 593646, 791340, 438259, 1343926, 2265842, 2572661, 1979312, 76992, 841221, 1846143, 34299, 2619579, 1414888, 497292, 133957, 857743, 1657258, 28392, 78474, 39260, 14363, 502284, 1189569, 741790, 1712169, 702355, 2016839, 1896490, 316153, 946629, 9502887, 73073, 1253522, 11680814, 170161, 363893, 231196, 3056793, 5100719, 1329657, 3359278, 3340634, 5486322, 9502887, 6046907]

theorem plane468GenLeaf0000 (x : Fin 62 → Int)
    (hroot : plane468GenOccSys.RootHolds x)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_51 : x 51 ≤ (0 : Int))
    (hUB_47 : x 47 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane468GenLeaf0000Refs i).resolveCoeff plane468GenOccSys j)
    (fun i => (plane468GenLeaf0000Refs i).resolveRhs plane468GenOccSys) plane468GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane468GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 5
  · exact hroot.hOcc 6
  · exact hroot.hOcc 8
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 29
  · exact hroot.hOcc 35
  · exact hroot.hOcc 53
  · exact hroot.hOcc 66
  · exact hroot.hOcc 69
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 97
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 113
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 142
  · exact hroot.hOcc 158
  · exact hroot.hOcc 162
  · exact hroot.hOcc 167
  · exact hroot.hOcc 169
  · exact hroot.hOcc 173
  · exact hroot.hOcc 195
  · exact hroot.hOcc 202
  · exact hroot.hOcc 207
  · exact hroot.hOcc 209
  · exact hroot.hOcc 213
  · exact hroot.hOcc 215
  · exact hroot.hOcc 219
  · exact hroot.hOcc 229
  · exact hroot.hOcc 232
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 242
  · exact hroot.hOcc 245
  · exact hroot.hOcc 247
  · exact hroot.hOcc 248
  · exact hroot.hOcc 249
  · change (∑ j, (-1 : Int) * x j) ≤ -plane468GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (45 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (50 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (54 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (56 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (60 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (28 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (51 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_51
  · change (∑ k, (if k = (47 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_47

end QiushiMatmul
