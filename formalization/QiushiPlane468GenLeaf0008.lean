import QiushiPlane468GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane468GenLeaf0008Refs : Fin 63 → RowRef 253 62 := ![.occ 18, .occ 26, .occ 29, .occ 32, .occ 37, .occ 42, .occ 45, .occ 48, .occ 53, .occ 64, .occ 66, .occ 76, .occ 77, .occ 79, .occ 82, .occ 103, .occ 105, .occ 115, .occ 116, .occ 118, .occ 120, .occ 124, .occ 130, .occ 139, .occ 151, .occ 158, .occ 167, .occ 169, .occ 180, .occ 183, .occ 184, .occ 193, .occ 194, .occ 195, .occ 199, .occ 201, .occ 202, .occ 203, .occ 207, .occ 223, .occ 224, .occ 226, .occ 229, .occ 232, .occ 243, .occ 245, .occ 247, .occ 250, .sumGe, .nonneg 7, .nonneg 8, .nonneg 10, .nonneg 15, .nonneg 20, .nonneg 37, .nonneg 46, .nonneg 50, .branchLe 28 (0), .branchGe 51 (1), .branchGe 2 (1), .branchGe 1 (1), .branchLe 11 (0), .branchGe 40 (1)]

def plane468GenLeaf0008Mult : Fin 63 → Nat := ![27025040, 4852344, 20157010, 4452638, 518716, 2587332, 3298884, 4426220, 704434, 2859692, 33138130, 196856, 19110164, 5590954, 5194304, 1783400, 9713854, 2780590, 6241110, 4603670, 2088554, 12241252, 13325682, 5675448, 1146894, 3935653, 4805832, 4059533, 6207266, 1687067, 13165660, 2063314, 1169323, 2160668, 4098054, 16242930, 516923, 3568665, 4323340, 6376511, 2867719, 8191981, 1661593, 6919562, 29927, 6041938, 5600448, 722982, 39566487, 29528668, 23962888, 21059444, 4445260, 8377048, 10158130, 5367110, 9773502, 16000058, 29156440, 40546976, 46014454, 11771042, 106713554]

theorem plane468GenLeaf0008 (x : Fin 62 → Int)
    (hroot : plane468GenOccSys.RootHolds x)
    (hLB_51 : (1 : Int) ≤ x 51)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane468GenLeaf0008Refs i).resolveCoeff plane468GenOccSys j)
    (fun i => (plane468GenLeaf0008Refs i).resolveRhs plane468GenOccSys) plane468GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane468GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 18
  · exact hroot.hOcc 26
  · exact hroot.hOcc 29
  · exact hroot.hOcc 32
  · exact hroot.hOcc 37
  · exact hroot.hOcc 42
  · exact hroot.hOcc 45
  · exact hroot.hOcc 48
  · exact hroot.hOcc 53
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 79
  · exact hroot.hOcc 82
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 118
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 130
  · exact hroot.hOcc 139
  · exact hroot.hOcc 151
  · exact hroot.hOcc 158
  · exact hroot.hOcc 167
  · exact hroot.hOcc 169
  · exact hroot.hOcc 180
  · exact hroot.hOcc 183
  · exact hroot.hOcc 184
  · exact hroot.hOcc 193
  · exact hroot.hOcc 194
  · exact hroot.hOcc 195
  · exact hroot.hOcc 199
  · exact hroot.hOcc 201
  · exact hroot.hOcc 202
  · exact hroot.hOcc 203
  · exact hroot.hOcc 207
  · exact hroot.hOcc 223
  · exact hroot.hOcc 224
  · exact hroot.hOcc 226
  · exact hroot.hOcc 229
  · exact hroot.hOcc 232
  · exact hroot.hOcc 243
  · exact hroot.hOcc 245
  · exact hroot.hOcc 247
  · exact hroot.hOcc 250
  · change (∑ j, (-1 : Int) * x j) ≤ -plane468GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (37 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (46 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (50 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (28 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_51
  · change (∑ k, (if k = (2 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (1 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (11 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
