import QiushiPlane462GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane462GenLeaf0006Refs : Fin 63 → RowRef 294 62 := ![.occ 3, .occ 13, .occ 14, .occ 31, .occ 42, .occ 49, .occ 62, .occ 67, .occ 77, .occ 78, .occ 80, .occ 81, .occ 86, .occ 87, .occ 88, .occ 91, .occ 94, .occ 99, .occ 100, .occ 102, .occ 103, .occ 109, .occ 112, .occ 114, .occ 115, .occ 120, .occ 121, .occ 130, .occ 133, .occ 134, .occ 138, .occ 145, .occ 146, .occ 150, .occ 160, .occ 193, .occ 200, .occ 202, .occ 205, .occ 207, .occ 214, .occ 219, .occ 231, .occ 233, .occ 239, .occ 244, .occ 249, .occ 256, .occ 259, .occ 260, .sumGe, .nonneg 7, .nonneg 12, .nonneg 15, .nonneg 25, .nonneg 38, .nonneg 41, .branchGe 3 (1), .branchLe 5 (0), .branchLe 2 (0), .branchLe 43 (0), .branchLe 4 (0), .branchGe 9 (1)]

def plane462GenLeaf0006Mult : Fin 63 → Nat := ![3936, 1272, 2064, 10008, 17544, 8616, 10800, 7008, 5244, 6760, 12200, 372, 18960, 1176, 2484, 1500, 8208, 9758, 2758, 2486, 11014, 7008, 2628, 3105, 2270, 6483, 3248, 2376, 3722, 7896, 3300, 6417, 1863, 1514, 5182, 1817, 439, 374, 8134, 6096, 1740, 684, 1164, 1330, 1298, 1692, 1988, 2140, 240, 2988, 34560, 45816, 20112, 27072, 27072, 1104, 39072, 11232, 27552, 27576, 32304, 27552, 12192]

theorem plane462GenLeaf0006 (x : Fin 62 → Int)
    (hroot : plane462GenOccSys.RootHolds x)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane462GenLeaf0006Refs i).resolveCoeff plane462GenOccSys j)
    (fun i => (plane462GenLeaf0006Refs i).resolveRhs plane462GenOccSys) plane462GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane462GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 3
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 31
  · exact hroot.hOcc 42
  · exact hroot.hOcc 49
  · exact hroot.hOcc 62
  · exact hroot.hOcc 67
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 88
  · exact hroot.hOcc 91
  · exact hroot.hOcc 94
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 138
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · exact hroot.hOcc 150
  · exact hroot.hOcc 160
  · exact hroot.hOcc 193
  · exact hroot.hOcc 200
  · exact hroot.hOcc 202
  · exact hroot.hOcc 205
  · exact hroot.hOcc 207
  · exact hroot.hOcc 214
  · exact hroot.hOcc 219
  · exact hroot.hOcc 231
  · exact hroot.hOcc 233
  · exact hroot.hOcc 239
  · exact hroot.hOcc 244
  · exact hroot.hOcc 249
  · exact hroot.hOcc 256
  · exact hroot.hOcc 259
  · exact hroot.hOcc 260
  · change (∑ j, (-1 : Int) * x j) ≤ -plane462GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (12 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (15 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (25 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (38 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (41 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (3 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3
  · change (∑ k, (if k = (5 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (2 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (43 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (4 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (9 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9

end QiushiMatmul
