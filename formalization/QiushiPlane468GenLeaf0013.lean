import QiushiPlane468GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane468GenLeaf0013Refs : Fin 63 → RowRef 253 62 := ![.occ 5, .occ 8, .occ 12, .occ 17, .occ 21, .occ 26, .occ 33, .occ 47, .occ 54, .occ 56, .occ 66, .occ 69, .occ 74, .occ 84, .occ 89, .occ 90, .occ 103, .occ 109, .occ 116, .occ 121, .occ 122, .occ 124, .occ 130, .occ 135, .occ 144, .occ 158, .occ 162, .occ 165, .occ 173, .occ 176, .occ 181, .occ 188, .occ 191, .occ 192, .occ 193, .occ 216, .occ 220, .occ 222, .occ 224, .occ 229, .occ 239, .occ 244, .occ 247, .occ 248, .occ 249, .sumGe, .nonneg 7, .nonneg 10, .nonneg 18, .nonneg 20, .nonneg 30, .nonneg 32, .nonneg 39, .nonneg 42, .nonneg 45, .nonneg 46, .nonneg 50, .nonneg 53, .nonneg 56, .nonneg 57, .nonneg 58, .branchGe 28 (1), .branchGe 36 (1)]

def plane468GenLeaf0013Mult : Fin 63 → Nat := ![337460, 562329, 194725, 281964, 778575, 190851, 248296, 399893, 308234, 139675, 69933, 321146, 529971, 387149, 123598, 297150, 703996, 503274, 154856, 156258, 184701, 173640, 92804, 295382, 156588, 85062, 35733, 49136, 205380, 291882, 64675, 40575, 144307, 185885, 349456, 168973, 84683, 192070, 171512, 170872, 20331, 21773, 305359, 43423, 353122, 1328530, 547023, 179240, 191756, 520868, 571305, 62774, 736106, 251706, 554668, 117406, 248459, 495992, 270299, 62128, 146646, 2861325, 3612878]

theorem plane468GenLeaf0013 (x : Fin 62 → Int)
    (hroot : plane468GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_36 : (1 : Int) ≤ x 36)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane468GenLeaf0013Refs i).resolveCoeff plane468GenOccSys j)
    (fun i => (plane468GenLeaf0013Refs i).resolveRhs plane468GenOccSys) plane468GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane468GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 8
  · exact hroot.hOcc 12
  · exact hroot.hOcc 17
  · exact hroot.hOcc 21
  · exact hroot.hOcc 26
  · exact hroot.hOcc 33
  · exact hroot.hOcc 47
  · exact hroot.hOcc 54
  · exact hroot.hOcc 56
  · exact hroot.hOcc 66
  · exact hroot.hOcc 69
  · exact hroot.hOcc 74
  · exact hroot.hOcc 84
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 103
  · exact hroot.hOcc 109
  · exact hroot.hOcc 116
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 144
  · exact hroot.hOcc 158
  · exact hroot.hOcc 162
  · exact hroot.hOcc 165
  · exact hroot.hOcc 173
  · exact hroot.hOcc 176
  · exact hroot.hOcc 181
  · exact hroot.hOcc 188
  · exact hroot.hOcc 191
  · exact hroot.hOcc 192
  · exact hroot.hOcc 193
  · exact hroot.hOcc 216
  · exact hroot.hOcc 220
  · exact hroot.hOcc 222
  · exact hroot.hOcc 224
  · exact hroot.hOcc 229
  · exact hroot.hOcc 239
  · exact hroot.hOcc 244
  · exact hroot.hOcc 247
  · exact hroot.hOcc 248
  · exact hroot.hOcc 249
  · change (∑ j, (-1 : Int) * x j) ≤ -plane468GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (18 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (32 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (42 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (45 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (46 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (50 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (56 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (58 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (28 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (36 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36

end QiushiMatmul
