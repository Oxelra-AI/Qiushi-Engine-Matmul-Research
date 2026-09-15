import QiushiPlane456GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane456GenLeaf0001Refs : Fin 64 → RowRef 248 63 := ![.occ 2, .occ 3, .occ 7, .occ 9, .occ 11, .occ 13, .occ 26, .occ 34, .occ 35, .occ 42, .occ 45, .occ 47, .occ 55, .occ 60, .occ 65, .occ 70, .occ 72, .occ 81, .occ 82, .occ 89, .occ 91, .occ 93, .occ 95, .occ 98, .occ 100, .occ 104, .occ 107, .occ 108, .occ 118, .occ 126, .occ 132, .occ 134, .occ 138, .occ 142, .occ 152, .occ 164, .occ 168, .occ 170, .occ 181, .occ 191, .occ 199, .occ 200, .occ 208, .occ 226, .occ 230, .occ 234, .occ 238, .occ 240, .occ 241, .sumGe, .nonneg 21, .nonneg 22, .nonneg 26, .nonneg 29, .nonneg 37, .nonneg 38, .nonneg 41, .nonneg 53, .branchLe 24 (0), .branchLe 31 (0), .branchLe 57 (0), .branchLe 54 (0), .branchLe 9 (0), .branchGe 10 (1)]

def plane456GenLeaf0001Mult : Fin 64 → Nat := ![101175, 98774, 11765, 7940, 9671, 34523, 28667, 4661, 2349, 6377, 9740, 27234, 10537, 13322, 42020, 23891, 34297, 27351, 34555, 21177, 27950, 31275, 15484, 11924, 12587, 23636, 42935, 3528, 7556, 9754, 33262, 25645, 15712, 7379, 2585, 29517, 13275, 15256, 14854, 14084, 20012, 2674, 14533, 1186, 12119, 12239, 1345, 9981, 22652, 113687, 55880, 37890, 100296, 64390, 9604, 83939, 33419, 49394, 30698, 70856, 77451, 89881, 103706, 355070]

theorem plane456GenLeaf0001 (x : Fin 63 → Int)
    (hroot : plane456GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_57 : x 57 ≤ (0 : Int))
    (hUB_54 : x 54 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane456GenLeaf0001Refs i).resolveCoeff plane456GenOccSys j)
    (fun i => (plane456GenLeaf0001Refs i).resolveRhs plane456GenOccSys) plane456GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane456GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 2
  · exact hroot.hOcc 3
  · exact hroot.hOcc 7
  · exact hroot.hOcc 9
  · exact hroot.hOcc 11
  · exact hroot.hOcc 13
  · exact hroot.hOcc 26
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 42
  · exact hroot.hOcc 45
  · exact hroot.hOcc 47
  · exact hroot.hOcc 55
  · exact hroot.hOcc 60
  · exact hroot.hOcc 65
  · exact hroot.hOcc 70
  · exact hroot.hOcc 72
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 89
  · exact hroot.hOcc 91
  · exact hroot.hOcc 93
  · exact hroot.hOcc 95
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 118
  · exact hroot.hOcc 126
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 152
  · exact hroot.hOcc 164
  · exact hroot.hOcc 168
  · exact hroot.hOcc 170
  · exact hroot.hOcc 181
  · exact hroot.hOcc 191
  · exact hroot.hOcc 199
  · exact hroot.hOcc 200
  · exact hroot.hOcc 208
  · exact hroot.hOcc 226
  · exact hroot.hOcc 230
  · exact hroot.hOcc 234
  · exact hroot.hOcc 238
  · exact hroot.hOcc 240
  · exact hroot.hOcc 241
  · change (∑ j, (-1 : Int) * x j) ≤ -plane456GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (22 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (26 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (29 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (37 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (38 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (41 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (53 : Fin 63) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (24 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (31 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (57 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_57
  · change (∑ k, (if k = (54 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_54
  · change (∑ k, (if k = (9 : Fin 63) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (10 : Fin 63) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
