import QiushiPlane472GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane472GenLeaf0008Refs : Fin 34 → RowRef 242 62 := ![.occ 2, .occ 7, .occ 8, .occ 10, .occ 31, .occ 50, .occ 63, .occ 65, .occ 70, .occ 71, .occ 84, .occ 124, .occ 125, .occ 135, .occ 150, .occ 152, .occ 159, .occ 160, .occ 180, .occ 191, .occ 207, .occ 208, .occ 215, .occ 241, .sumGe, .nonneg 24, .nonneg 27, .nonneg 30, .nonneg 42, .nonneg 45, .nonneg 57, .nonneg 61, .branchLe 60 (0), .branchGe 4 (1)]

def plane472GenLeaf0008Mult : Fin 34 → Nat := ![10, 1, 8, 10, 10, 7, 10, 9, 1, 1, 4, 9, 1, 3, 1, 3, 1, 2, 3, 6, 6, 2, 1, 1, 10, 7, 7, 2, 6, 6, 4, 4, 3, 98]

theorem plane472GenLeaf0008 (x : Fin 62 → Int)
    (hroot : plane472GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_60 : x 60 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane472GenLeaf0008Refs i).resolveCoeff plane472GenOccSys j)
    (fun i => (plane472GenLeaf0008Refs i).resolveRhs plane472GenOccSys) plane472GenLeaf0008Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane472GenLeaf0008Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 7
  · exact hroot.hOcc 8
  · exact hroot.hOcc 10
  · exact hroot.hOcc 31
  · exact hroot.hOcc 50
  · exact hroot.hOcc 63
  · exact hroot.hOcc 65
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 84
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 135
  · exact hroot.hOcc 150
  · exact hroot.hOcc 152
  · exact hroot.hOcc 159
  · exact hroot.hOcc 160
  · exact hroot.hOcc 180
  · exact hroot.hOcc 191
  · exact hroot.hOcc 207
  · exact hroot.hOcc 208
  · exact hroot.hOcc 215
  · exact hroot.hOcc 241
  · change (∑ j, (-1 : Int) * x j) ≤ -plane472GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (24 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (27 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (42 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (45 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (57 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (61 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (60 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (4 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
