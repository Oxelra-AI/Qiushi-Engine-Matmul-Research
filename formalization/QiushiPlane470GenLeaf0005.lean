import QiushiPlane470GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane470GenLeaf0005Refs : Fin 64 → RowRef 232 63 := ![.occ 2, .occ 6, .occ 8, .occ 12, .occ 24, .occ 26, .occ 28, .occ 39, .occ 40, .occ 56, .occ 61, .occ 72, .occ 73, .occ 74, .occ 80, .occ 95, .occ 97, .occ 98, .occ 106, .occ 107, .occ 110, .occ 111, .occ 112, .occ 122, .occ 126, .occ 131, .occ 136, .occ 140, .occ 144, .occ 145, .occ 170, .occ 174, .occ 175, .occ 179, .occ 183, .occ 184, .occ 200, .occ 203, .occ 210, .occ 216, .occ 222, .occ 229, .sumGe, .nonneg 4, .nonneg 5, .nonneg 7, .nonneg 8, .nonneg 10, .nonneg 11, .nonneg 16, .nonneg 17, .nonneg 21, .nonneg 44, .nonneg 45, .nonneg 48, .nonneg 50, .nonneg 51, .nonneg 54, .nonneg 57, .nonneg 59, .nonneg 60, .nonneg 61, .branchLe 12 (0), .branchGe 25 (1)]

def plane470GenLeaf0005Mult : Fin 64 → Nat := ![10914, 20359, 75945, 81175, 414, 51246, 11909, 23830, 6066, 88068, 89151, 9488, 20223, 10425, 15234, 3833, 71822, 1832, 1362, 46113, 6786, 16395, 19524, 4380, 13852, 71098, 9931, 17918, 2769, 2458, 22866, 7722, 4544, 36403, 10077, 4638, 30343, 2449, 1861, 3018, 38715, 4704, 96304, 4638, 7860, 33704, 27510, 55651, 7237, 68481, 34146, 9641, 21480, 32480, 480, 11283, 8918, 7971, 2871, 5218, 36330, 569, 96304, 662032]

theorem plane470GenLeaf0005 (x : Fin 63 → Int)
    (hroot : plane470GenOccSys.RootHolds x)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_60 : x 60 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane470GenLeaf0005Refs i).resolveCoeff plane470GenOccSys j)
    (fun i => (plane470GenLeaf0005Refs i).resolveRhs plane470GenOccSys) plane470GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane470GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 6
  · exact hroot.hOcc 8
  · exact hroot.hOcc 12
  · exact hroot.hOcc 24
  · exact hroot.hOcc 26
  · exact hroot.hOcc 28
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 56
  · exact hroot.hOcc 61
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 80
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 122
  · exact hroot.hOcc 126
  · exact hroot.hOcc 131
  · exact hroot.hOcc 136
  · exact hroot.hOcc 140
  · exact hroot.hOcc 144
  · exact hroot.hOcc 145
  · exact hroot.hOcc 170
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 179
  · exact hroot.hOcc 183
  · exact hroot.hOcc 184
  · exact hroot.hOcc 200
  · exact hroot.hOcc 203
  · exact hroot.hOcc 210
  · exact hroot.hOcc 216
  · exact hroot.hOcc 222
  · exact hroot.hOcc 229
  · change (∑ j, (-1 : Int) * x j) ≤ -plane470GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (5 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (7 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (16 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (44 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (45 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (48 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (50 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (51 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (54 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (57 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (59 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (60 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (61 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (12 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (25 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
