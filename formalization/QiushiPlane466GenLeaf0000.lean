import QiushiPlane466GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane466GenLeaf0000Refs : Fin 51 → RowRef 210 50 := ![.occ 20, .occ 44, .occ 45, .occ 49, .occ 54, .occ 61, .occ 62, .occ 64, .occ 72, .occ 73, .occ 79, .occ 81, .occ 83, .occ 86, .occ 88, .occ 94, .occ 98, .occ 99, .occ 100, .occ 102, .occ 106, .occ 107, .occ 111, .occ 114, .occ 116, .occ 119, .occ 120, .occ 124, .occ 129, .occ 134, .occ 142, .occ 152, .occ 159, .occ 164, .occ 167, .occ 172, .occ 183, .occ 184, .occ 188, .occ 196, .occ 197, .occ 205, .occ 209, .sumGe, .nonneg 0, .nonneg 32, .branchLe 24 (0), .branchLe 19 (0), .branchLe 26 (0), .branchLe 28 (0), .branchLe 7 (0)]

def plane466GenLeaf0000Mult : Fin 51 → Nat := ![224025, 341543, 45545, 867688, 560158, 544760, 614832, 1274145, 472174, 202439, 1170707, 7047, 1303617, 359267, 560482, 418278, 115887, 69559, 1619080, 413052, 130024, 191974, 518610, 537605, 1176618, 535302, 45185, 1002675, 635071, 752645, 61956, 221243, 843864, 9736, 350460, 1210484, 503929, 283767, 54982, 570957, 687028, 560836, 255555, 3875144, 4887051, 2282309, 2507860, 3820162, 3608716, 3100979, 2607368]

theorem plane466GenLeaf0000 (x : Fin 50 → Int)
    (hroot : plane466GenOccSys.RootHolds x)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane466GenLeaf0000Refs i).resolveCoeff plane466GenOccSys j)
    (fun i => (plane466GenLeaf0000Refs i).resolveRhs plane466GenOccSys) plane466GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane466GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 20
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 49
  · exact hroot.hOcc 54
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 64
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 83
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 94
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 142
  · exact hroot.hOcc 152
  · exact hroot.hOcc 159
  · exact hroot.hOcc 164
  · exact hroot.hOcc 167
  · exact hroot.hOcc 172
  · exact hroot.hOcc 183
  · exact hroot.hOcc 184
  · exact hroot.hOcc 188
  · exact hroot.hOcc 196
  · exact hroot.hOcc 197
  · exact hroot.hOcc 205
  · exact hroot.hOcc 209
  · change (∑ j, (-1 : Int) * x j) ≤ -plane466GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (24 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (19 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (26 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (28 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (7 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7

end QiushiMatmul
