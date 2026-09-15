import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0025Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 99, .occ 135, .occ 147, .occ 148, .occ 150, .occ 152, .occ 163, .occ 166, .occ 177, .occ 183, .occ 190, .occ 195, .occ 207, .occ 210, .occ 213, .occ 224, .occ 228, .occ 232, .occ 233, .occ 239, .occ 247, .occ 251, .occ 257, .occ 265, .occ 281, .occ 283, .occ 287, .occ 297, .occ 312, .occ 316, .occ 335, .occ 337, .occ 376, .occ 392, .occ 411, .sumGe, .nonneg 0, .branchLe 28 (0), .branchGe 21 (1), .branchLe 32 (0), .branchGe 25 (1)]

def plane485GenLeaf0025Mult : Fin 42 → Nat := ![57638, 341323, 161667, 62470, 991, 270537, 12623, 5298, 157054, 142182, 89991, 83041, 52245, 234448, 106346, 88031, 116812, 47047, 53063, 70747, 6158, 12305, 19787, 6465, 137679, 13818, 64868, 22573, 42606, 46222, 160759, 168715, 54496, 12623, 94963, 24331, 478426, 422884, 285257, 1096779, 290867, 897033]

theorem plane485GenLeaf0025 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0025Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0025Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0025Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0025Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 99
  · exact hroot.hOcc 135
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 150
  · exact hroot.hOcc 152
  · exact hroot.hOcc 163
  · exact hroot.hOcc 166
  · exact hroot.hOcc 177
  · exact hroot.hOcc 183
  · exact hroot.hOcc 190
  · exact hroot.hOcc 195
  · exact hroot.hOcc 207
  · exact hroot.hOcc 210
  · exact hroot.hOcc 213
  · exact hroot.hOcc 224
  · exact hroot.hOcc 228
  · exact hroot.hOcc 232
  · exact hroot.hOcc 233
  · exact hroot.hOcc 239
  · exact hroot.hOcc 247
  · exact hroot.hOcc 251
  · exact hroot.hOcc 257
  · exact hroot.hOcc 265
  · exact hroot.hOcc 281
  · exact hroot.hOcc 283
  · exact hroot.hOcc 287
  · exact hroot.hOcc 297
  · exact hroot.hOcc 312
  · exact hroot.hOcc 316
  · exact hroot.hOcc 335
  · exact hroot.hOcc 337
  · exact hroot.hOcc 376
  · exact hroot.hOcc 392
  · exact hroot.hOcc 411
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (32 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (25 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
