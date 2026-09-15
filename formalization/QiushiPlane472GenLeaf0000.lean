import QiushiPlane472GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane472GenLeaf0000Refs : Fin 63 → RowRef 242 62 := ![.occ 1, .occ 23, .occ 36, .occ 38, .occ 42, .occ 43, .occ 46, .occ 48, .occ 55, .occ 56, .occ 57, .occ 60, .occ 61, .occ 64, .occ 69, .occ 71, .occ 75, .occ 76, .occ 80, .occ 82, .occ 87, .occ 91, .occ 94, .occ 95, .occ 96, .occ 99, .occ 101, .occ 104, .occ 119, .occ 131, .occ 132, .occ 134, .occ 136, .occ 165, .occ 168, .occ 170, .occ 174, .occ 175, .occ 176, .occ 178, .occ 198, .occ 206, .occ 213, .occ 217, .occ 219, .occ 226, .occ 227, .occ 228, .occ 231, .occ 234, .sumGe, .nonneg 13, .nonneg 16, .nonneg 40, .nonneg 48, .nonneg 49, .nonneg 55, .branchLe 60 (0), .branchLe 4 (0), .branchLe 33 (0), .branchLe 11 (0), .branchLe 21 (0), .branchLe 51 (0)]

def plane472GenLeaf0000Mult : Fin 63 → Nat := ![21847874, 12731322, 12998022, 19762462, 32176930, 22170250, 4851094, 13661982, 24125226, 4685000, 11311170, 7609076, 3758514, 57403032, 3217656, 17714216, 24505876, 36963092, 14522968, 17921662, 22640524, 26971168, 21384682, 16426594, 1132936, 37213576, 4519094, 9505260, 9388874, 7374249, 4364397, 16967497, 29552419, 27404804, 13938345, 801169, 1054763, 19816780, 19739858, 19189288, 15780220, 3529684, 18329534, 16541988, 7959953, 17972005, 7921737, 14553371, 2536746, 9366473, 132385712, 12409890, 31378816, 502242, 36097486, 29929472, 22139000, 129848966, 126319282, 87467402, 93368616, 92743976, 93619086]

theorem plane472GenLeaf0000 (x : Fin 62 → Int)
    (hroot : plane472GenOccSys.RootHolds x)
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_51 : x 51 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane472GenLeaf0000Refs i).resolveCoeff plane472GenOccSys j)
    (fun i => (plane472GenLeaf0000Refs i).resolveRhs plane472GenOccSys) plane472GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane472GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 23
  · exact hroot.hOcc 36
  · exact hroot.hOcc 38
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 46
  · exact hroot.hOcc 48
  · exact hroot.hOcc 55
  · exact hroot.hOcc 56
  · exact hroot.hOcc 57
  · exact hroot.hOcc 60
  · exact hroot.hOcc 61
  · exact hroot.hOcc 64
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 80
  · exact hroot.hOcc 82
  · exact hroot.hOcc 87
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 96
  · exact hroot.hOcc 99
  · exact hroot.hOcc 101
  · exact hroot.hOcc 104
  · exact hroot.hOcc 119
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 165
  · exact hroot.hOcc 168
  · exact hroot.hOcc 170
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 178
  · exact hroot.hOcc 198
  · exact hroot.hOcc 206
  · exact hroot.hOcc 213
  · exact hroot.hOcc 217
  · exact hroot.hOcc 219
  · exact hroot.hOcc 226
  · exact hroot.hOcc 227
  · exact hroot.hOcc 228
  · exact hroot.hOcc 231
  · exact hroot.hOcc 234
  · change (∑ j, (-1 : Int) * x j) ≤ -plane472GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (16 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (40 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (48 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (49 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 49
  · change (∑ k, (if k = (55 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (60 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (4 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (33 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (11 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (21 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (51 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_51

end QiushiMatmul
