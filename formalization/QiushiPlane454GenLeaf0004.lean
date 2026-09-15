import QiushiPlane454GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane454GenLeaf0004Refs : Fin 56 → RowRef 174 55 := ![.occ 8, .occ 15, .occ 18, .occ 20, .occ 22, .occ 25, .occ 29, .occ 30, .occ 33, .occ 39, .occ 42, .occ 52, .occ 60, .occ 64, .occ 67, .occ 69, .occ 73, .occ 75, .occ 80, .occ 81, .occ 83, .occ 86, .occ 89, .occ 90, .occ 91, .occ 95, .occ 100, .occ 112, .occ 116, .occ 119, .occ 120, .occ 130, .occ 135, .occ 136, .occ 139, .occ 142, .occ 143, .occ 147, .occ 155, .occ 159, .occ 168, .occ 172, .sumGe, .nonneg 15, .nonneg 17, .nonneg 24, .nonneg 27, .nonneg 29, .nonneg 37, .nonneg 48, .nonneg 52, .nonneg 54, .branchLe 2 (0), .branchGe 4 (1), .branchGe 5 (1), .branchLe 16 (0)]

def plane454GenLeaf0004Mult : Fin 56 → Nat := ![22690, 6697, 8004, 4329, 21191, 32098, 6988, 11278, 31307, 4346, 14629, 13135, 1178, 35574, 25155, 2934, 15728, 9921, 7161, 4552, 919, 5165, 9005, 12232, 33302, 6776, 1753, 11607, 6410, 8124, 4227, 1286, 13291, 1046, 646, 3973, 13712, 21070, 1382, 4831, 3316, 4279, 47014, 20687, 32965, 5093, 15820, 2623, 9806, 1321, 16329, 11446, 21859, 181405, 37613, 47014]

theorem plane454GenLeaf0004 (x : Fin 55 → Int)
    (hroot : plane454GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane454GenLeaf0004Refs i).resolveCoeff plane454GenOccSys j)
    (fun i => (plane454GenLeaf0004Refs i).resolveRhs plane454GenOccSys) plane454GenLeaf0004Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane454GenLeaf0004Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 15
  · exact hroot.hOcc 18
  · exact hroot.hOcc 20
  · exact hroot.hOcc 22
  · exact hroot.hOcc 25
  · exact hroot.hOcc 29
  · exact hroot.hOcc 30
  · exact hroot.hOcc 33
  · exact hroot.hOcc 39
  · exact hroot.hOcc 42
  · exact hroot.hOcc 52
  · exact hroot.hOcc 60
  · exact hroot.hOcc 64
  · exact hroot.hOcc 67
  · exact hroot.hOcc 69
  · exact hroot.hOcc 73
  · exact hroot.hOcc 75
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 83
  · exact hroot.hOcc 86
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 95
  · exact hroot.hOcc 100
  · exact hroot.hOcc 112
  · exact hroot.hOcc 116
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 147
  · exact hroot.hOcc 155
  · exact hroot.hOcc 159
  · exact hroot.hOcc 168
  · exact hroot.hOcc 172
  · change (∑ j, (-1 : Int) * x j) ≤ -plane454GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (17 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (24 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (27 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (29 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (37 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (48 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (52 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (54 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (2 : Fin 55) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (4 : Fin 55) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (5 : Fin 55) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (16 : Fin 55) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16

end QiushiMatmul
