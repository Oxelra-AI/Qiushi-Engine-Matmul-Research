import QiushiPlane472GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane472GenLeaf0007Refs : Fin 63 → RowRef 242 62 := ![.occ 1, .occ 6, .occ 12, .occ 14, .occ 17, .occ 19, .occ 20, .occ 28, .occ 34, .occ 35, .occ 39, .occ 72, .occ 73, .occ 74, .occ 75, .occ 77, .occ 78, .occ 86, .occ 88, .occ 94, .occ 95, .occ 97, .occ 98, .occ 100, .occ 102, .occ 104, .occ 114, .occ 115, .occ 116, .occ 117, .occ 128, .occ 131, .occ 132, .occ 133, .occ 137, .occ 156, .occ 162, .occ 165, .occ 168, .occ 171, .occ 174, .occ 175, .occ 176, .occ 184, .occ 191, .occ 227, .occ 238, .occ 239, .sumGe, .nonneg 10, .nonneg 16, .nonneg 20, .nonneg 36, .nonneg 42, .nonneg 44, .nonneg 48, .nonneg 50, .nonneg 52, .nonneg 53, .nonneg 59, .branchLe 60 (0), .branchLe 4 (0), .branchGe 33 (1)]

def plane472GenLeaf0007Mult : Fin 63 → Nat := ![134629, 8571, 111612, 150046, 28379, 2532, 29682, 183314, 41497, 226463, 24579, 20213, 205831, 7910, 74985, 4793, 14753, 146747, 23663, 38229, 175227, 10515, 25400, 58124, 30814, 33360, 158538, 52995, 14345, 3637, 101609, 8822, 13007, 8322, 95253, 50481, 57134, 30564, 22431, 2380, 8173, 9424, 20666, 22482, 147847, 5506, 6014, 6372, 241901, 84445, 141377, 27978, 94279, 13782, 32005, 54368, 123776, 11167, 67618, 9652, 87682, 31187, 1773503]

theorem plane472GenLeaf0007 (x : Fin 62 → Int)
    (hroot : plane472GenOccSys.RootHolds x)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hUB_60 : x 60 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane472GenLeaf0007Refs i).resolveCoeff plane472GenOccSys j)
    (fun i => (plane472GenLeaf0007Refs i).resolveRhs plane472GenOccSys) plane472GenLeaf0007Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane472GenLeaf0007Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 1
  · exact hroot.hOcc 6
  · exact hroot.hOcc 12
  · exact hroot.hOcc 14
  · exact hroot.hOcc 17
  · exact hroot.hOcc 19
  · exact hroot.hOcc 20
  · exact hroot.hOcc 28
  · exact hroot.hOcc 34
  · exact hroot.hOcc 35
  · exact hroot.hOcc 39
  · exact hroot.hOcc 72
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 94
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 104
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 128
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 137
  · exact hroot.hOcc 156
  · exact hroot.hOcc 162
  · exact hroot.hOcc 165
  · exact hroot.hOcc 168
  · exact hroot.hOcc 171
  · exact hroot.hOcc 174
  · exact hroot.hOcc 175
  · exact hroot.hOcc 176
  · exact hroot.hOcc 184
  · exact hroot.hOcc 191
  · exact hroot.hOcc 227
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · change (∑ j, (-1 : Int) * x j) ≤ -plane472GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (16 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (36 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (42 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (44 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (48 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (50 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (59 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 59
  · change (∑ k, (if k = (60 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_60
  · change (∑ k, (if k = (4 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (33 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33

end QiushiMatmul
