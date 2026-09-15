import QiushiPlane456GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane456GenLeaf0000Refs : Fin 64 → RowRef 248 63 := ![.occ 4, .occ 12, .occ 18, .occ 19, .occ 21, .occ 31, .occ 32, .occ 58, .occ 59, .occ 65, .occ 67, .occ 72, .occ 81, .occ 82, .occ 83, .occ 88, .occ 93, .occ 94, .occ 95, .occ 106, .occ 107, .occ 120, .occ 121, .occ 122, .occ 125, .occ 129, .occ 132, .occ 134, .occ 135, .occ 155, .occ 162, .occ 165, .occ 168, .occ 195, .occ 200, .occ 208, .occ 214, .occ 215, .occ 220, .occ 221, .occ 230, .occ 233, .occ 235, .occ 237, .occ 240, .occ 241, .occ 242, .occ 245, .sumGe, .nonneg 7, .nonneg 21, .nonneg 28, .nonneg 29, .nonneg 42, .nonneg 48, .nonneg 51, .nonneg 53, .nonneg 59, .branchLe 24 (0), .branchLe 31 (0), .branchLe 57 (0), .branchLe 54 (0), .branchLe 9 (0), .branchLe 10 (0)]

def plane456GenLeaf0000Mult : Fin 64 → Nat := ![6219016, 23570836, 12451246, 7656986, 67962076, 14959312, 41604170, 5621480, 40904890, 31024516, 56249174, 98797438, 30524780, 62173684, 51598812, 36281352, 86025904, 23225670, 10561200, 44611486, 96184858, 2225090, 27059516, 13470014, 20205552, 37622326, 45155196, 38710118, 37083676, 39657638, 121226, 17162728, 59488050, 15065950, 54133010, 32482666, 32451908, 6790110, 2082414, 5995148, 69341729, 53383628, 14463490, 19710129, 67500624, 13028492, 10858383, 635193, 291631272, 12502432, 31984920, 14738292, 185083030, 23030420, 87041438, 1768612, 20049204, 84684990, 90018546, 278602780, 194650640, 291631272, 172583482, 248034268]

theorem plane456GenLeaf0000 (x : Fin 63 → Int)
    (hroot : plane456GenOccSys.RootHolds x)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_57 : x 57 ≤ (0 : Int))
    (hUB_54 : x 54 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane456GenLeaf0000Refs i).resolveCoeff plane456GenOccSys j)
    (fun i => (plane456GenLeaf0000Refs i).resolveRhs plane456GenOccSys) plane456GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane456GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 12
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 21
  · exact hroot.hOcc 31
  · exact hroot.hOcc 32
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 65
  · exact hroot.hOcc 67
  · exact hroot.hOcc 72
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 88
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 155
  · exact hroot.hOcc 162
  · exact hroot.hOcc 165
  · exact hroot.hOcc 168
  · exact hroot.hOcc 195
  · exact hroot.hOcc 200
  · exact hroot.hOcc 208
  · exact hroot.hOcc 214
  · exact hroot.hOcc 215
  · exact hroot.hOcc 220
  · exact hroot.hOcc 221
  · exact hroot.hOcc 230
  · exact hroot.hOcc 233
  · exact hroot.hOcc 235
  · exact hroot.hOcc 237
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · exact hroot.hOcc 242
  · exact hroot.hOcc 245
  · change (∑ j, (-1 : Int) * x j) ≤ -plane456GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (28 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (29 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (42 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (53 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (31 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (57 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_57
  · change (∑ k, (if k = (54 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_54
  · change (∑ k, (if k = (9 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10

end QiushiMatmul
