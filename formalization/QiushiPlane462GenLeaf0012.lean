import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0012Refs : Fin 62 → RowRef 294 62 := ![.occ 1, .occ 2, .occ 19, .occ 43, .occ 51, .occ 52, .occ 55, .occ 62, .occ 67, .occ 68, .occ 71, .occ 73, .occ 81, .occ 88, .occ 89, .occ 96, .occ 97, .occ 100, .occ 102, .occ 109, .occ 110, .occ 118, .occ 123, .occ 129, .occ 130, .occ 136, .occ 139, .occ 140, .occ 141, .occ 143, .occ 147, .occ 151, .occ 164, .occ 174, .occ 175, .occ 182, .occ 188, .occ 193, .occ 199, .occ 214, .occ 217, .occ 223, .occ 240, .occ 242, .occ 247, .occ 252, .occ 255, .occ 256, .occ 262, .occ 274, .occ 293, .sumGe, .nonneg 0, .nonneg 7, .nonneg 8, .nonneg 39, .nonneg 41, .nonneg 47, .branchGe 3 (1), .branchGe 5 (1), .branchLe 24 (0), .branchGe 45 (1)]

def plane462GenLeaf0012Mult : Fin 62 → Nat := ![52, 72, 8, 24, 6, 10, 4, 44, 52, 6, 18, 2, 22, 8, 24, 8, 6, 4, 12, 12, 2, 11, 3, 20, 15, 12, 4, 2, 5, 1, 2, 13, 12, 21, 61, 52, 20, 26, 19, 25, 17, 6, 46, 26, 32, 19, 34, 42, 10, 8, 8, 152, 48, 48, 40, 4, 204, 56, 284, 92, 152, 504]

theorem plane462GenLeaf0012 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_45 : (1 : Int) ≤ x 45)
    (hUB_24 : x 24 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0012Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0012Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0012Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0012Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 2
  · exact hroot.hOcc 19
  · exact hroot.hOcc 43
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 55
  · exact hroot.hOcc 62
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 71
  · exact hroot.hOcc 73
  · exact hroot.hOcc 81
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 96
  · exact hroot.hOcc 97
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 118
  · exact hroot.hOcc 123
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 143
  · exact hroot.hOcc 147
  · exact hroot.hOcc 151
  · exact hroot.hOcc 164
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 182
  · exact hroot.hOcc 188
  · exact hroot.hOcc 193
  · exact hroot.hOcc 199
  · exact hroot.hOcc 214
  · exact hroot.hOcc 217
  · exact hroot.hOcc 223
  · exact hroot.hOcc 240
  · exact hroot.hOcc 242
  · exact hroot.hOcc 247
  · exact hroot.hOcc 252
  · exact hroot.hOcc 255
  · exact hroot.hOcc 256
  · exact hroot.hOcc 262
  · exact hroot.hOcc 274
  · exact hroot.hOcc 293
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (41 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (47 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (5 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (24 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (45 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_45

end QiushiMatmul
