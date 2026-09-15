import QiushiPlane472GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane472GenLeaf0005Refs : Fin 63 → RowRef 242 62 := ![.occ 4, .occ 5, .occ 9, .occ 13, .occ 15, .occ 25, .occ 33, .occ 34, .occ 46, .occ 59, .occ 68, .occ 69, .occ 75, .occ 76, .occ 80, .occ 84, .occ 88, .occ 89, .occ 94, .occ 101, .occ 102, .occ 117, .occ 122, .occ 155, .occ 168, .occ 171, .occ 173, .occ 174, .occ 175, .occ 177, .occ 196, .occ 197, .occ 201, .occ 203, .occ 210, .occ 211, .occ 216, .occ 226, .occ 227, .occ 228, .occ 234, .occ 235, .sumGe, .nonneg 16, .nonneg 24, .nonneg 27, .nonneg 30, .nonneg 40, .nonneg 42, .nonneg 45, .nonneg 48, .nonneg 49, .nonneg 53, .nonneg 55, .nonneg 58, .nonneg 61, .branchLe 60 (0), .branchLe 4 (0), .branchLe 33 (0), .branchGe 11 (1), .branchLe 28 (0), .branchGe 17 (1), .branchGe 26 (1)]

def plane472GenLeaf0005Mult : Fin 63 → Nat := ![25210, 52140, 51538, 1898, 10114, 12740, 3000, 24562, 64270, 35574, 5696, 87166, 23316, 15824, 15680, 60202, 18036, 8228, 19136, 27314, 26544, 53572, 802, 33548, 50076, 22414, 12264, 1194, 616, 5210, 10892, 882, 30758, 5546, 9084, 5680, 1150, 7251, 18918, 24487, 14033, 6545, 116556, 13948, 100170, 47404, 39226, 18146, 45268, 27390, 8994, 16590, 122, 3658, 33712, 46268, 105664, 56354, 23184, 129660, 66352, 80830, 386902]

theorem plane472GenLeaf0005 (x : Fin 62 → Int)
    (hroot : plane472GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane472GenLeaf0005Refs i).resolveCoeff plane472GenOccSys j)
    (fun i => (plane472GenLeaf0005Refs i).resolveRhs plane472GenOccSys) plane472GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane472GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 4
  · exact hroot.hOcc 5
  · exact hroot.hOcc 9
  · exact hroot.hOcc 13
  · exact hroot.hOcc 15
  · exact hroot.hOcc 25
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 46
  · exact hroot.hOcc 59
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 80
  · exact hroot.hOcc 84
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 94
  · exact hroot.hOcc 101
  · exact hroot.hOcc 102
  · exact hroot.hOcc 117
  · exact hroot.hOcc 122
  · exact hroot.hOcc 155
  · exact hroot.hOcc 168
  · exact hroot.hOcc 171
  · exact hroot.hOcc 173
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 177
  · exact hroot.hOcc 196
  · exact hroot.hOcc 197
  · exact hroot.hOcc 201
  · exact hroot.hOcc 203
  · exact hroot.hOcc 210
  · exact hroot.hOcc 211
  · exact hroot.hOcc 216
  · exact hroot.hOcc 226
  · exact hroot.hOcc 227
  · exact hroot.hOcc 228
  · exact hroot.hOcc 234
  · exact hroot.hOcc 235
  · change (∑ j, (-1 : Int) * x j) ≤ -plane472GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (24 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (27 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (42 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (45 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (48 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (49 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (55 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (58 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 58
  · change (∑ k, (if k = (61 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 61
  · change (∑ k, (if k = (60 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (4 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (33 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (11 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (28 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (17 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (26 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
