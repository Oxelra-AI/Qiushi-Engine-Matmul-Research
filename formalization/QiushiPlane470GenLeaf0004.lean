import QiushiPlane470GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane470GenLeaf0004Refs : Fin 64 → RowRef 232 63 := ![.occ 0, .occ 4, .occ 30, .occ 33, .occ 44, .occ 47, .occ 52, .occ 64, .occ 72, .occ 74, .occ 77, .occ 80, .occ 81, .occ 83, .occ 84, .occ 88, .occ 89, .occ 90, .occ 98, .occ 103, .occ 105, .occ 107, .occ 117, .occ 129, .occ 134, .occ 138, .occ 144, .occ 159, .occ 167, .occ 175, .occ 176, .occ 178, .occ 182, .occ 188, .occ 205, .occ 212, .occ 213, .occ 215, .occ 216, .occ 228, .occ 229, .sumGe, .nonneg 3, .nonneg 7, .nonneg 10, .nonneg 19, .nonneg 20, .nonneg 21, .nonneg 24, .nonneg 26, .nonneg 32, .nonneg 38, .nonneg 40, .nonneg 45, .nonneg 47, .nonneg 48, .nonneg 51, .nonneg 55, .nonneg 57, .nonneg 59, .branchLe 12 (0), .branchLe 60 (0), .branchLe 25 (0), .branchGe 15 (1)]

def plane470GenLeaf0004Mult : Fin 64 → Nat := ![3876, 3900, 943, 636, 2962, 3790, 4594, 850, 3500, 654, 669, 96, 1500, 153, 289, 1175, 537, 2512, 1733, 347, 1018, 246, 138, 303, 89, 1711, 575, 1355, 421, 2389, 58, 294, 182, 981, 38, 752, 254, 179, 405, 747, 1420, 4869, 1685, 810, 2188, 1226, 346, 1021, 197, 1708, 2682, 980, 1694, 483, 676, 1102, 2096, 3145, 443, 2186, 3438, 3709, 1751, 32108]

theorem plane470GenLeaf0004 (x : Fin 63 → Int)
    (hroot : plane470GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane470GenLeaf0004Refs i).resolveCoeff plane470GenOccSys j)
    (fun i => (plane470GenLeaf0004Refs i).resolveRhs plane470GenOccSys) plane470GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane470GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 0
  · exact hroot.hOcc 4
  · exact hroot.hOcc 30
  · exact hroot.hOcc 33
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 64
  · exact hroot.hOcc 72
  · exact hroot.hOcc 74
  · exact hroot.hOcc 77
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 98
  · exact hroot.hOcc 103
  · exact hroot.hOcc 105
  · exact hroot.hOcc 107
  · exact hroot.hOcc 117
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 138
  · exact hroot.hOcc 144
  · exact hroot.hOcc 159
  · exact hroot.hOcc 167
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 178
  · exact hroot.hOcc 182
  · exact hroot.hOcc 188
  · exact hroot.hOcc 205
  · exact hroot.hOcc 212
  · exact hroot.hOcc 213
  · exact hroot.hOcc 215
  · exact hroot.hOcc 216
  · exact hroot.hOcc 228
  · exact hroot.hOcc 229
  · change (∑ j, (-1 : Int) * x j) ≤ -plane470GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (7 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (19 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (24 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (32 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (40 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (45 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (47 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (55 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (57 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (12 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (60 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (25 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (15 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15

end QiushiMatmul
