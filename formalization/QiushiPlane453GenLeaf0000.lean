import QiushiPlane453GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane453GenLeaf0000Refs : Fin 51 → RowRef 210 50 := ![.occ 17, .occ 35, .occ 41, .occ 51, .occ 52, .occ 54, .occ 56, .occ 62, .occ 65, .occ 67, .occ 70, .occ 80, .occ 81, .occ 85, .occ 87, .occ 100, .occ 104, .occ 105, .occ 106, .occ 108, .occ 109, .occ 118, .occ 122, .occ 123, .occ 124, .occ 125, .occ 133, .occ 134, .occ 142, .occ 147, .occ 150, .occ 169, .occ 172, .occ 180, .occ 193, .occ 195, .occ 198, .occ 199, .occ 200, .occ 207, .occ 209, .sumGe, .nonneg 22, .nonneg 23, .nonneg 24, .nonneg 28, .nonneg 47, .branchLe 35 (0), .branchLe 5 (1), .branchLe 15 (0), .branchLe 9 (0)]

def plane453GenLeaf0000Mult : Fin 51 → Nat := ![86146, 17488, 2476, 18134, 62292, 207070, 127828, 16748, 23796, 149312, 66126, 70836, 292, 30880, 69664, 19302, 136824, 103310, 57266, 107520, 18600, 3232, 12798, 43584, 22610, 53244, 68310, 50742, 2188, 18528, 101038, 116780, 29108, 36826, 34554, 45699, 107507, 20734, 130068, 80391, 98143, 516902, 31786, 80430, 100346, 9834, 204958, 516902, 114856, 516902, 413592]

theorem plane453GenLeaf0000 (x : Fin 50 → Int)
    (hroot : plane453GenOccSys.RootHolds x)
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (1 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane453GenLeaf0000Refs i).resolveCoeff plane453GenOccSys j)
    (fun i => (plane453GenLeaf0000Refs i).resolveRhs plane453GenOccSys) plane453GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane453GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 17
  · exact hroot.hOcc 35
  · exact hroot.hOcc 41
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 54
  · exact hroot.hOcc 56
  · exact hroot.hOcc 62
  · exact hroot.hOcc 65
  · exact hroot.hOcc 67
  · exact hroot.hOcc 70
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 87
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 108
  · exact hroot.hOcc 109
  · exact hroot.hOcc 118
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 142
  · exact hroot.hOcc 147
  · exact hroot.hOcc 150
  · exact hroot.hOcc 169
  · exact hroot.hOcc 172
  · exact hroot.hOcc 180
  · exact hroot.hOcc 193
  · exact hroot.hOcc 195
  · exact hroot.hOcc 198
  · exact hroot.hOcc 199
  · exact hroot.hOcc 200
  · exact hroot.hOcc 207
  · exact hroot.hOcc 209
  · change (∑ j, (-1 : Int) * x j) ≤ -plane453GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (22 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (28 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (47 : Fin 50) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (35 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (5 : Fin 50) then (1 : Int) else 0) * x k) ≤ (1 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (15 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (9 : Fin 50) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
