import QiushiPlane458GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane458GenLeaf0008Refs : Fin 57 → RowRef 203 56 := ![.occ 10, .occ 20, .occ 22, .occ 25, .occ 41, .occ 42, .occ 43, .occ 44, .occ 56, .occ 58, .occ 59, .occ 63, .occ 68, .occ 71, .occ 73, .occ 74, .occ 75, .occ 86, .occ 87, .occ 89, .occ 90, .occ 94, .occ 95, .occ 96, .occ 102, .occ 106, .occ 109, .occ 111, .occ 114, .occ 118, .occ 120, .occ 121, .occ 125, .occ 129, .occ 131, .occ 148, .occ 156, .occ 160, .occ 163, .occ 168, .occ 174, .occ 180, .occ 187, .sumGe, .nonneg 12, .nonneg 19, .nonneg 20, .nonneg 22, .nonneg 29, .nonneg 36, .nonneg 37, .nonneg 39, .nonneg 41, .nonneg 48, .nonneg 53, .branchGe 46 (1), .branchGe 10 (1)]

def plane458GenLeaf0008Mult : Fin 57 → Nat := ![1756, 1365, 357, 619, 2189, 1693, 1606, 1732, 2516, 2971, 457, 395, 617, 603, 1146, 1544, 1153, 251, 581, 848, 1193, 154, 455, 1051, 127, 953, 163, 306, 1305, 100, 298, 201, 51, 620, 86, 226, 73, 621, 274, 972, 1215, 1201, 1063, 2971, 1336, 137, 442, 889, 1121, 1913, 818, 453, 136, 1040, 1666, 12190, 12885]

theorem plane458GenLeaf0008 (x : Fin 56 → Int)
    (hroot : plane458GenOccSys.RootHolds x)
    (hLB_46 : (1 : Int) ≤ x 46)
    (hLB_10 : (1 : Int) ≤ x 10)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane458GenLeaf0008Refs i).resolveCoeff plane458GenOccSys j)
    (fun i => (plane458GenLeaf0008Refs i).resolveRhs plane458GenOccSys) plane458GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane458GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · exact hroot.hOcc 20
  · exact hroot.hOcc 22
  · exact hroot.hOcc 25
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 56
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 63
  · exact hroot.hOcc 68
  · exact hroot.hOcc 71
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 102
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 118
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 125
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 148
  · exact hroot.hOcc 156
  · exact hroot.hOcc 160
  · exact hroot.hOcc 163
  · exact hroot.hOcc 168
  · exact hroot.hOcc 174
  · exact hroot.hOcc 180
  · exact hroot.hOcc 187
  · change (∑ j, (-1 : Int) * x j) ≤ -plane458GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (12 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (19 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (22 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (29 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (36 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (37 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (39 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (41 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (48 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (53 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (46 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_46
  · change (∑ k, (if k = (10 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
