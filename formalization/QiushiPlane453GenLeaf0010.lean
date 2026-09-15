import QiushiPlane453GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane453GenLeaf0010Refs : Fin 49 → RowRef 210 50 := ![.occ 14, .occ 42, .occ 43, .occ 44, .occ 48, .occ 52, .occ 55, .occ 61, .occ 67, .occ 68, .occ 70, .occ 72, .occ 75, .occ 79, .occ 80, .occ 82, .occ 83, .occ 89, .occ 95, .occ 103, .occ 104, .occ 105, .occ 106, .occ 113, .occ 140, .occ 142, .occ 150, .occ 155, .occ 166, .occ 169, .occ 170, .occ 172, .occ 173, .occ 174, .occ 191, .occ 205, .occ 206, .sumGe, .nonneg 0, .nonneg 7, .nonneg 13, .nonneg 22, .nonneg 24, .nonneg 29, .nonneg 47, .nonneg 48, .branchLe 35 (0), .branchGe 5 (2), .branchGe 41 (1)]

def plane453GenLeaf0010Mult : Fin 49 → Nat := ![52, 469, 461, 493, 285, 253, 464, 300, 197, 461, 112, 388, 310, 25, 821, 163, 86, 35, 23, 52, 734, 186, 25, 384, 139, 249, 49, 15, 25, 597, 86, 138, 112, 1, 634, 25, 25, 871, 721, 86, 324, 598, 772, 338, 199, 239, 621, 1583, 4062]

theorem plane453GenLeaf0010 (x : Fin 50 → Int)
    (hroot : plane453GenOccSys.RootHolds x)
    (hLB_5 : (2 : Int) ≤ x 5)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane453GenLeaf0010Refs i).resolveCoeff plane453GenOccSys j)
    (fun i => (plane453GenLeaf0010Refs i).resolveRhs plane453GenOccSys) plane453GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane453GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 48
  · exact hroot.hOcc 52
  · exact hroot.hOcc 55
  · exact hroot.hOcc 61
  · exact hroot.hOcc 67
  · exact hroot.hOcc 68
  · exact hroot.hOcc 70
  · exact hroot.hOcc 72
  · exact hroot.hOcc 75
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 82
  · exact hroot.hOcc 83
  · exact hroot.hOcc 89
  · exact hroot.hOcc 95
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 113
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 150
  · exact hroot.hOcc 155
  · exact hroot.hOcc 166
  · exact hroot.hOcc 169
  · exact hroot.hOcc 170
  · exact hroot.hOcc 172
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 191
  · exact hroot.hOcc 205
  · exact hroot.hOcc 206
  · change (∑ j, (-1 : Int) * x j) ≤ -plane453GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (7 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (13 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (22 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (24 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (47 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (48 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(2 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (41 : Fin 50) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41

end QiushiMatmul
