import QiushiPlane461GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane461GenLeaf0000Refs : Fin 61 → RowRef 151 62 := ![.occ 11, .occ 12, .occ 13, .occ 14, .occ 20, .occ 21, .occ 22, .occ 24, .occ 25, .occ 26, .occ 28, .occ 30, .occ 33, .occ 34, .occ 36, .occ 37, .occ 38, .occ 39, .occ 40, .occ 41, .occ 42, .occ 43, .occ 57, .occ 58, .occ 62, .occ 63, .occ 75, .occ 76, .occ 79, .occ 86, .occ 87, .occ 90, .occ 94, .occ 99, .occ 100, .occ 101, .occ 103, .occ 119, .occ 124, .occ 132, .occ 134, .occ 137, .occ 141, .occ 142, .occ 143, .occ 144, .occ 145, .occ 146, .sumGe, .nonneg 6, .nonneg 9, .nonneg 15, .nonneg 25, .nonneg 35, .nonneg 37, .nonneg 45, .nonneg 51, .nonneg 53, .branchLe 16 (0), .branchLe 7 (0), .branchLe 22 (0)]

def plane461GenLeaf0000Mult : Fin 61 → Nat := ![888, 2252, 2820, 784, 1664, 800, 4236, 3296, 1776, 2800, 1964, 10080, 3618, 2562, 4432, 5024, 1902, 1198, 6408, 5976, 918, 1942, 4146, 2034, 1456, 2320, 4004, 3060, 80, 6880, 4040, 80, 3754, 1120, 562, 78, 486, 656, 2286, 2480, 434, 1104, 4000, 4240, 2213, 695, 227, 1665, 20080, 3040, 2840, 4272, 15768, 5320, 1412, 2668, 7076, 4084, 18188, 10000, 17172]

theorem plane461GenLeaf0000 (x : Fin 62 → Int)
    (hroot : plane461GenOccSys.RootHolds x)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane461GenLeaf0000Refs i).resolveCoeff plane461GenOccSys j)
    (fun i => (plane461GenLeaf0000Refs i).resolveRhs plane461GenOccSys) plane461GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane461GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 11
  · exact hroot.hOcc 12
  · exact hroot.hOcc 13
  · exact hroot.hOcc 14
  · exact hroot.hOcc 20
  · exact hroot.hOcc 21
  · exact hroot.hOcc 22
  · exact hroot.hOcc 24
  · exact hroot.hOcc 25
  · exact hroot.hOcc 26
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 33
  · exact hroot.hOcc 34
  · exact hroot.hOcc 36
  · exact hroot.hOcc 37
  · exact hroot.hOcc 38
  · exact hroot.hOcc 39
  · exact hroot.hOcc 40
  · exact hroot.hOcc 41
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 57
  · exact hroot.hOcc 58
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 79
  · exact hroot.hOcc 86
  · exact hroot.hOcc 87
  · exact hroot.hOcc 90
  · exact hroot.hOcc 94
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 101
  · exact hroot.hOcc 103
  · exact hroot.hOcc 119
  · exact hroot.hOcc 124
  · exact hroot.hOcc 132
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 144
  · exact hroot.hOcc 145
  · exact hroot.hOcc 146
  · change (∑ j, (-1 : Int) * x j) ≤ -plane461GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (9 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (15 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (25 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (35 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 35
  · change (∑ k, (if k = (37 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (45 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (51 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (16 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (7 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (22 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22

end QiushiMatmul
