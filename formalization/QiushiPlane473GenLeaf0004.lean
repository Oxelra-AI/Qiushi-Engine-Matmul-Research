import QiushiPlane473GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane473GenLeaf0004Refs : Fin 60 → RowRef 153 59 := ![.occ 10, .occ 12, .occ 16, .occ 18, .occ 19, .occ 25, .occ 28, .occ 30, .occ 36, .occ 44, .occ 45, .occ 46, .occ 47, .occ 52, .occ 55, .occ 58, .occ 62, .occ 69, .occ 70, .occ 71, .occ 78, .occ 79, .occ 81, .occ 82, .occ 85, .occ 86, .occ 89, .occ 92, .occ 93, .occ 95, .occ 96, .occ 101, .occ 103, .occ 106, .occ 107, .occ 115, .occ 127, .occ 129, .occ 132, .occ 138, .occ 140, .occ 141, .occ 142, .occ 143, .occ 144, .occ 146, .sumGe, .nonneg 12, .nonneg 16, .nonneg 19, .nonneg 24, .nonneg 28, .nonneg 36, .nonneg 38, .nonneg 46, .nonneg 49, .nonneg 54, .nonneg 56, .nonneg 57, .branchGe 40 (1)]

def plane473GenLeaf0004Mult : Fin 60 → Nat := ![33152, 9056, 106205, 148052, 285288, 242075, 350680, 604111, 163754, 330469, 182518, 328964, 75326, 83974, 44390, 179750, 231558, 259297, 73865, 78319, 203322, 12725, 41739, 358002, 379402, 21873, 344011, 20627, 50598, 91962, 82577, 55580, 284062, 31598, 26736, 47632, 171152, 46515, 41080, 1420, 18526, 43137, 26223, 106127, 75949, 39342, 706283, 135668, 62426, 432040, 39346, 293567, 192620, 514210, 512006, 263517, 356830, 402596, 444750, 3068405]

theorem plane473GenLeaf0004 (x : Fin 59 → Int)
    (hroot : plane473GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane473GenLeaf0004Refs i).resolveCoeff plane473GenOccSys j)
    (fun i => (plane473GenLeaf0004Refs i).resolveRhs plane473GenOccSys) plane473GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane473GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 10
  · exact hroot.hOcc 12
  · exact hroot.hOcc 16
  · exact hroot.hOcc 18
  · exact hroot.hOcc 19
  · exact hroot.hOcc 25
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 36
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 46
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 55
  · exact hroot.hOcc 58
  · exact hroot.hOcc 62
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 71
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 89
  · exact hroot.hOcc 92
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 101
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 115
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 132
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 144
  · exact hroot.hOcc 146
  · change (∑ j, (-1 : Int) * x j) ≤ -plane473GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (12 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (16 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (19 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (24 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (28 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (36 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (38 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (46 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (49 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (54 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (56 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (57 : Fin 59) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (40 : Fin 59) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
