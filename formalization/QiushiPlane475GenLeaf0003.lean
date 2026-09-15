import QiushiPlane475GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane475GenLeaf0003Refs : Fin 57 → RowRef 126 56 := ![.occ 7, .occ 10, .occ 11, .occ 13, .occ 15, .occ 18, .occ 21, .occ 24, .occ 26, .occ 28, .occ 32, .occ 33, .occ 34, .occ 37, .occ 46, .occ 47, .occ 50, .occ 51, .occ 56, .occ 57, .occ 58, .occ 59, .occ 65, .occ 70, .occ 73, .occ 75, .occ 78, .occ 89, .occ 91, .occ 94, .occ 96, .occ 100, .occ 105, .occ 106, .occ 108, .occ 110, .occ 111, .occ 114, .occ 115, .occ 116, .occ 120, .occ 124, .occ 125, .sumGe, .nonneg 7, .nonneg 10, .nonneg 12, .nonneg 22, .nonneg 24, .nonneg 30, .nonneg 33, .nonneg 36, .nonneg 44, .nonneg 50, .nonneg 51, .branchGe 34 (1), .branchGe 27 (1)]

def plane475GenLeaf0003Mult : Fin 57 → Nat := ![16567, 19300, 15441, 7066, 12479, 6553, 9848, 17236, 28483, 16975, 1794, 3967, 19851, 3506, 12834, 6991, 15271, 808, 726, 3511, 3821, 17192, 11020, 9230, 10044, 6858, 6711, 3058, 1755, 3459, 5147, 1662, 11538, 2547, 1377, 6406, 5437, 6361, 10649, 570, 691, 733, 2017, 30500, 5959, 4504, 21385, 18647, 10960, 12318, 1036, 4106, 4304, 2641, 11667, 92319, 110720]

theorem plane475GenLeaf0003 (x : Fin 56 → Int)
    (hroot : plane475GenOccSys.RootHolds x)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_27 : (1 : Int) ≤ x 27)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane475GenLeaf0003Refs i).resolveCoeff plane475GenOccSys j)
    (fun i => (plane475GenLeaf0003Refs i).resolveRhs plane475GenOccSys) plane475GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane475GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 10
  · exact hroot.hOcc 11
  · exact hroot.hOcc 13
  · exact hroot.hOcc 15
  · exact hroot.hOcc 18
  · exact hroot.hOcc 21
  · exact hroot.hOcc 24
  · exact hroot.hOcc 26
  · exact hroot.hOcc 28
  · exact hroot.hOcc 32
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 37
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 59
  · exact hroot.hOcc 65
  · exact hroot.hOcc 70
  · exact hroot.hOcc 73
  · exact hroot.hOcc 75
  · exact hroot.hOcc 78
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 96
  · exact hroot.hOcc 100
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · change (∑ j, (-1 : Int) * x j) ≤ -plane475GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (10 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (12 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (22 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (24 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (30 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (33 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (44 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (50 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (51 : Fin 56) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (34 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (27 : Fin 56) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27

end QiushiMatmul
