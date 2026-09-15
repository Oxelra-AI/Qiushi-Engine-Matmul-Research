import QiushiPlane464GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane464GenLeaf0000Refs : Fin 51 → RowRef 202 50 := ![.occ 15, .occ 16, .occ 22, .occ 36, .occ 51, .occ 60, .occ 68, .occ 69, .occ 74, .occ 75, .occ 80, .occ 81, .occ 85, .occ 87, .occ 90, .occ 93, .occ 95, .occ 98, .occ 104, .occ 106, .occ 107, .occ 118, .occ 119, .occ 126, .occ 127, .occ 130, .occ 132, .occ 134, .occ 147, .occ 152, .occ 155, .occ 156, .occ 161, .occ 166, .occ 177, .occ 179, .occ 185, .occ 187, .occ 188, .occ 190, .occ 192, .occ 193, .occ 198, .sumGe, .nonneg 0, .nonneg 27, .nonneg 29, .nonneg 32, .branchLe 1 (0), .branchLe 15 (0), .branchLe 5 (0)]

def plane464GenLeaf0000Mult : Fin 51 → Nat := ![3842500, 2584048, 720484, 1921776, 558968, 5145930, 2071754, 2869560, 695714, 651362, 7038448, 4287002, 1054872, 5949348, 2117646, 7654200, 1427468, 2806416, 5209026, 4560482, 1839220, 2282916, 2042438, 1656485, 1090005, 2139002, 5924620, 3736532, 3752022, 2459106, 476625, 3059110, 5070225, 779691, 1453543, 4074335, 1603062, 1039515, 109319, 370283, 1970315, 2871045, 2557110, 21296778, 13043696, 2135836, 1793272, 16903276, 19886980, 16713352, 16736296]

theorem plane464GenLeaf0000 (x : Fin 50 → Int)
    (hroot : plane464GenOccSys.RootHolds x)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane464GenLeaf0000Refs i).resolveCoeff plane464GenOccSys j)
    (fun i => (plane464GenLeaf0000Refs i).resolveRhs plane464GenOccSys) plane464GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane464GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 15
  · exact hroot.hOcc 16
  · exact hroot.hOcc 22
  · exact hroot.hOcc 36
  · exact hroot.hOcc 51
  · exact hroot.hOcc 60
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 87
  · exact hroot.hOcc 90
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 98
  · exact hroot.hOcc 104
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 118
  · exact hroot.hOcc 119
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 147
  · exact hroot.hOcc 152
  · exact hroot.hOcc 155
  · exact hroot.hOcc 156
  · exact hroot.hOcc 161
  · exact hroot.hOcc 166
  · exact hroot.hOcc 177
  · exact hroot.hOcc 179
  · exact hroot.hOcc 185
  · exact hroot.hOcc 187
  · exact hroot.hOcc 188
  · exact hroot.hOcc 190
  · exact hroot.hOcc 192
  · exact hroot.hOcc 193
  · exact hroot.hOcc 198
  · change (∑ j, (-1 : Int) * x j) ≤ -plane464GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (27 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (29 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (32 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (1 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (15 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (5 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5

end QiushiMatmul
