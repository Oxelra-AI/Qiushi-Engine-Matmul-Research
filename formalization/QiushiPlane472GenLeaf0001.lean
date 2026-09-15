import QiushiPlane472GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane472GenLeaf0001Refs : Fin 63 → RowRef 242 62 := ![.occ 1, .occ 15, .occ 25, .occ 26, .occ 27, .occ 33, .occ 42, .occ 43, .occ 45, .occ 47, .occ 58, .occ 60, .occ 64, .occ 75, .occ 76, .occ 78, .occ 79, .occ 80, .occ 81, .occ 83, .occ 88, .occ 93, .occ 94, .occ 95, .occ 99, .occ 101, .occ 102, .occ 113, .occ 132, .occ 134, .occ 136, .occ 140, .occ 149, .occ 158, .occ 163, .occ 165, .occ 168, .occ 174, .occ 176, .occ 198, .occ 201, .occ 206, .occ 226, .occ 228, .occ 234, .occ 235, .occ 236, .occ 240, .sumGe, .nonneg 13, .nonneg 18, .nonneg 32, .nonneg 40, .nonneg 44, .nonneg 45, .nonneg 53, .nonneg 57, .branchLe 60 (0), .branchLe 4 (0), .branchLe 33 (0), .branchLe 11 (0), .branchLe 21 (0), .branchGe 51 (1)]

def plane472GenLeaf0001Mult : Fin 63 → Nat := ![18047154, 11582178, 19370568, 10523482, 22817634, 2142286, 7498750, 8386192, 13134358, 13089274, 3336450, 11848982, 12652140, 4165176, 6863706, 5988340, 1430412, 7348090, 1946190, 39567506, 15851362, 9546362, 7406666, 152586, 7817110, 5056458, 28491844, 13426966, 1336346, 198455, 5993539, 5190006, 929626, 6686917, 7721297, 6107839, 5800069, 23881260, 8861057, 7258903, 4748379, 572440, 9716470, 4951431, 1363574, 1494403, 9945469, 6298127, 61223319, 10884764, 18833278, 3192146, 9759994, 9891682, 4049894, 1543512, 2939206, 54925192, 54352752, 48824830, 44832016, 57435716, 157978708]

theorem plane472GenLeaf0001 (x : Fin 62 → Int)
    (hroot : plane472GenOccSys.RootHolds x)
    (hLB_51 : (1 : Int) ≤ x 51)
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane472GenLeaf0001Refs i).resolveCoeff plane472GenOccSys j)
    (fun i => (plane472GenLeaf0001Refs i).resolveRhs plane472GenOccSys) plane472GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane472GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 15
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 27
  · exact hroot.hOcc 33
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 45
  · exact hroot.hOcc 47
  · exact hroot.hOcc 58
  · exact hroot.hOcc 60
  · exact hroot.hOcc 64
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 83
  · exact hroot.hOcc 88
  · exact hroot.hOcc 93
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 113
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 140
  · exact hroot.hOcc 149
  · exact hroot.hOcc 158
  · exact hroot.hOcc 163
  · exact hroot.hOcc 165
  · exact hroot.hOcc 168
  · exact hroot.hOcc 174
  · exact hroot.hOcc 176
  · exact hroot.hOcc 198
  · exact hroot.hOcc 201
  · exact hroot.hOcc 206
  · exact hroot.hOcc 226
  · exact hroot.hOcc 228
  · exact hroot.hOcc 234
  · exact hroot.hOcc 235
  · exact hroot.hOcc 236
  · exact hroot.hOcc 240
  · change (∑ j, (-1 : Int) * x j) ≤ -plane472GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (18 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (44 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (45 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (60 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (4 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (33 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (11 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (21 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_51

end QiushiMatmul
