import QiushiPlane457GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane457GenLeaf0005Refs : Fin 50 → RowRef 178 49 := ![.occ 21, .occ 35, .occ 37, .occ 48, .occ 49, .occ 60, .occ 64, .occ 68, .occ 69, .occ 73, .occ 75, .occ 76, .occ 77, .occ 78, .occ 83, .occ 84, .occ 87, .occ 89, .occ 92, .occ 95, .occ 98, .occ 101, .occ 107, .occ 108, .occ 112, .occ 117, .occ 118, .occ 124, .occ 125, .occ 126, .occ 127, .occ 138, .occ 150, .occ 151, .occ 158, .occ 159, .occ 166, .sumGe, .nonneg 8, .nonneg 11, .nonneg 18, .nonneg 20, .nonneg 33, .nonneg 39, .nonneg 40, .nonneg 46, .nonneg 48, .branchGe 3 (1), .branchLe 23 (0), .branchGe 26 (1)]

def plane457GenLeaf0005Mult : Fin 50 → Nat := ![1319, 1725, 709, 2984, 2680, 1107, 2786, 1683, 1814, 1814, 465, 757, 1639, 1931, 883, 884, 3378, 2536, 2790, 1683, 1814, 229, 1683, 622, 174, 50, 2736, 1640, 422, 182, 394, 355, 515, 537, 635, 54, 592, 4604, 2194, 2614, 263, 2439, 491, 2394, 1063, 1902, 55, 8633, 1632, 21152]

theorem plane457GenLeaf0005 (x : Fin 49 → Int)
    (hroot : plane457GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_23 : x 23 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane457GenLeaf0005Refs i).resolveCoeff plane457GenOccSys j)
    (fun i => (plane457GenLeaf0005Refs i).resolveRhs plane457GenOccSys) plane457GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane457GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 21
  · exact hroot.hOcc 35
  · exact hroot.hOcc 37
  · exact hroot.hOcc 48
  · exact hroot.hOcc 49
  · exact hroot.hOcc 60
  · exact hroot.hOcc 64
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 73
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 83
  · exact hroot.hOcc 84
  · exact hroot.hOcc 87
  · exact hroot.hOcc 89
  · exact hroot.hOcc 92
  · exact hroot.hOcc 95
  · exact hroot.hOcc 98
  · exact hroot.hOcc 101
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 112
  · exact hroot.hOcc 117
  · exact hroot.hOcc 118
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 138
  · exact hroot.hOcc 150
  · exact hroot.hOcc 151
  · exact hroot.hOcc 158
  · exact hroot.hOcc 159
  · exact hroot.hOcc 166
  · change (∑ j, (-1 : Int) * x j) ≤ -plane457GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (18 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (20 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (33 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (39 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (46 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (48 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (3 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
