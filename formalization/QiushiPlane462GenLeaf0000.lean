import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0000Refs : Fin 62 → RowRef 294 62 := ![.occ 1, .occ 3, .occ 11, .occ 12, .occ 27, .occ 29, .occ 68, .occ 71, .occ 73, .occ 74, .occ 77, .occ 81, .occ 85, .occ 86, .occ 88, .occ 100, .occ 103, .occ 109, .occ 115, .occ 116, .occ 117, .occ 118, .occ 121, .occ 132, .occ 135, .occ 143, .occ 145, .occ 151, .occ 153, .occ 157, .occ 160, .occ 161, .occ 162, .occ 170, .occ 172, .occ 192, .occ 202, .occ 204, .occ 210, .occ 215, .occ 219, .occ 225, .occ 241, .occ 245, .occ 249, .occ 267, .occ 269, .occ 273, .occ 279, .occ 280, .occ 281, .occ 284, .sumGe, .nonneg 7, .nonneg 10, .nonneg 12, .nonneg 20, .nonneg 26, .nonneg 51, .branchLe 3 (0), .branchLe 34 (1), .branchLe 28 (0)]

def plane462GenLeaf0000Mult : Fin 62 → Nat := ![56, 56, 156, 112, 248, 208, 378, 276, 100, 114, 288, 128, 258, 256, 374, 222, 280, 222, 86, 152, 217, 204, 71, 4, 88, 175, 231, 20, 113, 165, 110, 34, 64, 24, 156, 82, 2, 98, 112, 274, 30, 98, 100, 234, 30, 156, 70, 214, 32, 100, 116, 158, 1568, 264, 24, 168, 24, 168, 304, 1568, 1536, 1568]

theorem plane462GenLeaf0000 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (1 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0000Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0000Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 3
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 27
  · exact hroot.hOcc 29
  · exact hroot.hOcc 68
  · exact hroot.hOcc 71
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 77
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 109
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 118
  · exact hroot.hOcc 121
  · exact hroot.hOcc 132
  · exact hroot.hOcc 135
  · exact hroot.hOcc 143
  · exact hroot.hOcc 145
  · exact hroot.hOcc 151
  · exact hroot.hOcc 153
  · exact hroot.hOcc 157
  · exact hroot.hOcc 160
  · exact hroot.hOcc 161
  · exact hroot.hOcc 162
  · exact hroot.hOcc 170
  · exact hroot.hOcc 172
  · exact hroot.hOcc 192
  · exact hroot.hOcc 202
  · exact hroot.hOcc 204
  · exact hroot.hOcc 210
  · exact hroot.hOcc 215
  · exact hroot.hOcc 219
  · exact hroot.hOcc 225
  · exact hroot.hOcc 241
  · exact hroot.hOcc 245
  · exact hroot.hOcc 249
  · exact hroot.hOcc 267
  · exact hroot.hOcc 269
  · exact hroot.hOcc 273
  · exact hroot.hOcc 279
  · exact hroot.hOcc 280
  · exact hroot.hOcc 281
  · exact hroot.hOcc 284
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (12 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (26 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (3 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (34 : Fin 62) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (28 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
