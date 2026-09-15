import QiushiPlane456GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane456GenLeaf0002Refs : Fin 64 → RowRef 248 63 := ![.occ 2, .occ 5, .occ 16, .occ 44, .occ 46, .occ 47, .occ 57, .occ 59, .occ 65, .occ 72, .occ 75, .occ 76, .occ 81, .occ 83, .occ 90, .occ 91, .occ 93, .occ 94, .occ 100, .occ 107, .occ 108, .occ 118, .occ 119, .occ 134, .occ 135, .occ 145, .occ 155, .occ 163, .occ 164, .occ 168, .occ 169, .occ 170, .occ 174, .occ 176, .occ 200, .occ 201, .occ 208, .occ 209, .occ 218, .occ 221, .occ 228, .occ 235, .occ 237, .occ 239, .occ 240, .sumGe, .nonneg 20, .nonneg 26, .nonneg 29, .nonneg 32, .nonneg 37, .nonneg 38, .nonneg 44, .nonneg 48, .nonneg 49, .nonneg 53, .nonneg 55, .nonneg 59, .branchLe 24 (0), .branchLe 31 (0), .branchLe 57 (0), .branchLe 54 (0), .branchGe 9 (1), .branchLe 4 (0)]

def plane456GenLeaf0002Mult : Fin 64 → Nat := ![54771, 39104, 4923, 33433, 12007, 8187, 58174, 38566, 34774, 52464, 28727, 38839, 12058, 668, 52104, 10366, 38570, 29237, 41016, 62636, 5014, 4753, 1964, 11959, 54821, 39256, 3163, 16558, 9918, 15904, 5729, 10066, 30, 11520, 11469, 7928, 33743, 14764, 21902, 3177, 6569, 20538, 12935, 28667, 43525, 158053, 343, 25379, 18178, 21198, 26624, 60626, 25287, 53728, 50624, 46636, 23969, 35444, 73953, 117866, 127029, 136121, 291337, 137515]

theorem plane456GenLeaf0002 (x : Fin 63 → Int)
    (hroot : plane456GenOccSys.RootHolds x)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_57 : x 57 ≤ (0 : Int))
    (hUB_54 : x 54 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane456GenLeaf0002Refs i).resolveCoeff plane456GenOccSys j)
    (fun i => (plane456GenLeaf0002Refs i).resolveRhs plane456GenOccSys) plane456GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane456GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 5
  · exact hroot.hOcc 16
  · exact hroot.hOcc 44
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 57
  · exact hroot.hOcc 59
  · exact hroot.hOcc 65
  · exact hroot.hOcc 72
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 81
  · exact hroot.hOcc 83
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 100
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 145
  · exact hroot.hOcc 155
  · exact hroot.hOcc 163
  · exact hroot.hOcc 164
  · exact hroot.hOcc 168
  · exact hroot.hOcc 169
  · exact hroot.hOcc 170
  · exact hroot.hOcc 174
  · exact hroot.hOcc 176
  · exact hroot.hOcc 200
  · exact hroot.hOcc 201
  · exact hroot.hOcc 208
  · exact hroot.hOcc 209
  · exact hroot.hOcc 218
  · exact hroot.hOcc 221
  · exact hroot.hOcc 228
  · exact hroot.hOcc 235
  · exact hroot.hOcc 237
  · exact hroot.hOcc 239
  · exact hroot.hOcc 240
  · change (∑ j, (-1 : Int) * x j) ≤ -plane456GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (20 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (29 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (49 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (53 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (31 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (57 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_57
  · change (∑ k, (if k = (54 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_54
  · change (∑ k, (if k = (9 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (4 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
