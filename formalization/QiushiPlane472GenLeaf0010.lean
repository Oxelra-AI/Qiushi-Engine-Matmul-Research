import QiushiPlane472GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane472GenLeaf0010Refs : Fin 63 → RowRef 242 62 := ![.occ 5, .occ 10, .occ 15, .occ 44, .occ 52, .occ 54, .occ 65, .occ 76, .occ 80, .occ 84, .occ 87, .occ 95, .occ 99, .occ 102, .occ 106, .occ 108, .occ 109, .occ 110, .occ 111, .occ 112, .occ 113, .occ 115, .occ 121, .occ 146, .occ 151, .occ 161, .occ 167, .occ 175, .occ 176, .occ 186, .occ 188, .occ 190, .occ 196, .occ 203, .occ 205, .occ 214, .occ 221, .occ 229, .occ 231, .occ 232, .occ 233, .occ 239, .sumGe, .nonneg 7, .nonneg 10, .nonneg 18, .nonneg 22, .nonneg 24, .nonneg 27, .nonneg 30, .nonneg 39, .nonneg 40, .nonneg 42, .nonneg 44, .nonneg 50, .nonneg 52, .nonneg 55, .nonneg 57, .nonneg 58, .nonneg 61, .branchGe 60 (1), .branchLe 6 (0), .branchGe 5 (1)]

def plane472GenLeaf0010Mult : Fin 63 → Nat := ![93636, 21105, 58507, 952, 74555, 122402, 27658, 11876, 92468, 11927, 7840, 48720, 31487, 3347, 27427, 74878, 144250, 21641, 137530, 123965, 9498, 4756, 72691, 55102, 8580, 516, 14349, 22458, 4273, 33980, 29060, 21712, 83133, 16200, 7369, 34318, 61294, 263, 14067, 45861, 23836, 13863, 201731, 36951, 202401, 10963, 89539, 34318, 102708, 39978, 84143, 85735, 8687, 7765, 109667, 280547, 71019, 63960, 8539, 26838, 979779, 70269, 286906]

theorem plane472GenLeaf0010 (x : Fin 62 → Int)
    (hroot : plane472GenOccSys.RootHolds x)
    (hLB_60 : (1 : Int) ≤ x 60)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane472GenLeaf0010Refs i).resolveCoeff plane472GenOccSys j)
    (fun i => (plane472GenLeaf0010Refs i).resolveRhs plane472GenOccSys) plane472GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane472GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 10
  · exact hroot.hOcc 15
  · exact hroot.hOcc 44
  · exact hroot.hOcc 52
  · exact hroot.hOcc 54
  · exact hroot.hOcc 65
  · exact hroot.hOcc 76
  · exact hroot.hOcc 80
  · exact hroot.hOcc 84
  · exact hroot.hOcc 87
  · exact hroot.hOcc 95
  · exact hroot.hOcc 99
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 115
  · exact hroot.hOcc 121
  · exact hroot.hOcc 146
  · exact hroot.hOcc 151
  · exact hroot.hOcc 161
  · exact hroot.hOcc 167
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 186
  · exact hroot.hOcc 188
  · exact hroot.hOcc 190
  · exact hroot.hOcc 196
  · exact hroot.hOcc 203
  · exact hroot.hOcc 205
  · exact hroot.hOcc 214
  · exact hroot.hOcc 221
  · exact hroot.hOcc 229
  · exact hroot.hOcc 231
  · exact hroot.hOcc 232
  · exact hroot.hOcc 233
  · exact hroot.hOcc 239
  · change (∑ j, (-1 : Int) * x j) ≤ -plane472GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (18 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (22 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (24 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (27 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (42 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (50 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (55 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (58 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (61 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (60 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_60
  · change (∑ k, (if k = (6 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (5 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
