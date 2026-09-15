import QiushiPlane468GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane468GenLeaf0001Refs : Fin 63 → RowRef 253 62 := ![.occ 2, .occ 13, .occ 16, .occ 19, .occ 20, .occ 21, .occ 22, .occ 23, .occ 28, .occ 38, .occ 46, .occ 66, .occ 70, .occ 80, .occ 85, .occ 86, .occ 94, .occ 98, .occ 101, .occ 103, .occ 105, .occ 109, .occ 116, .occ 119, .occ 121, .occ 127, .occ 128, .occ 135, .occ 144, .occ 150, .occ 158, .occ 163, .occ 167, .occ 170, .occ 172, .occ 180, .occ 195, .occ 206, .occ 224, .occ 225, .occ 226, .occ 228, .occ 232, .occ 237, .occ 238, .occ 242, .occ 245, .occ 247, .sumGe, .nonneg 10, .nonneg 15, .nonneg 30, .nonneg 31, .nonneg 34, .nonneg 37, .nonneg 50, .nonneg 53, .nonneg 54, .nonneg 59, .nonneg 60, .branchLe 28 (0), .branchLe 51 (0), .branchGe 47 (1)]

def plane468GenLeaf0001Mult : Fin 63 → Nat := ![360292, 77620, 564472, 158953, 1217927, 896795, 378478, 1390527, 209969, 568201, 162367, 843302, 51570, 507949, 482966, 515208, 182438, 76232, 482288, 998336, 1071563, 306100, 179252, 1021862, 1383388, 30004, 433581, 424030, 504864, 433423, 519666, 70502, 177383, 43110, 12231, 387702, 261150, 186071, 124269, 177878, 830111, 245131, 135012, 51570, 273461, 286846, 380883, 183026, 2489272, 1702899, 492668, 603526, 1005699, 786264, 45271, 309152, 128422, 891236, 924764, 621381, 2063830, 2437702, 9985579]

theorem plane468GenLeaf0001 (x : Fin 62 → Int)
    (hroot : plane468GenOccSys.RootHolds x)
    (hLB_47 : (1 : Int) ≤ x 47)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_51 : x 51 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane468GenLeaf0001Refs i).resolveCoeff plane468GenOccSys j)
    (fun i => (plane468GenLeaf0001Refs i).resolveRhs plane468GenOccSys) plane468GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane468GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 13
  · exact hroot.hOcc 16
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 23
  · exact hroot.hOcc 28
  · exact hroot.hOcc 38
  · exact hroot.hOcc 46
  · exact hroot.hOcc 66
  · exact hroot.hOcc 70
  · exact hroot.hOcc 80
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 94
  · exact hroot.hOcc 98
  · exact hroot.hOcc 101
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 109
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 135
  · exact hroot.hOcc 144
  · exact hroot.hOcc 150
  · exact hroot.hOcc 158
  · exact hroot.hOcc 163
  · exact hroot.hOcc 167
  · exact hroot.hOcc 170
  · exact hroot.hOcc 172
  · exact hroot.hOcc 180
  · exact hroot.hOcc 195
  · exact hroot.hOcc 206
  · exact hroot.hOcc 224
  · exact hroot.hOcc 225
  · exact hroot.hOcc 226
  · exact hroot.hOcc 228
  · exact hroot.hOcc 232
  · exact hroot.hOcc 237
  · exact hroot.hOcc 238
  · exact hroot.hOcc 242
  · exact hroot.hOcc 245
  · exact hroot.hOcc 247
  · change (∑ j, (-1 : Int) * x j) ≤ -plane468GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (31 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (34 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (37 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (50 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (54 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (60 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (28 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (51 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_51
  · change (∑ k, (if k = (47 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_47

end QiushiMatmul
