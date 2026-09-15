import QiushiPlane454GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane454GenLeaf0005Refs : Fin 56 → RowRef 174 55 := ![.occ 8, .occ 10, .occ 12, .occ 18, .occ 28, .occ 30, .occ 44, .occ 51, .occ 52, .occ 53, .occ 56, .occ 62, .occ 63, .occ 64, .occ 66, .occ 67, .occ 69, .occ 71, .occ 81, .occ 85, .occ 91, .occ 96, .occ 100, .occ 102, .occ 103, .occ 106, .occ 107, .occ 111, .occ 118, .occ 130, .occ 132, .occ 133, .occ 147, .occ 152, .occ 154, .occ 158, .occ 160, .occ 163, .occ 173, .sumGe, .nonneg 2, .nonneg 15, .nonneg 17, .nonneg 24, .nonneg 27, .nonneg 29, .nonneg 33, .nonneg 37, .nonneg 41, .nonneg 45, .nonneg 51, .nonneg 52, .nonneg 53, .nonneg 54, .branchGe 4 (1), .branchGe 16 (1)]

def plane454GenLeaf0005Mult : Fin 56 → Nat := ![1098, 24, 458, 771, 2306, 430, 1044, 1488, 340, 2837, 184, 1822, 654, 810, 812, 1696, 822, 2934, 1150, 2442, 1344, 2436, 716, 985, 82, 194, 1415, 845, 1432, 288, 1444, 757, 158, 1036, 836, 616, 32, 502, 32, 3970, 980, 628, 506, 1784, 3317, 1953, 2030, 534, 484, 1000, 537, 2334, 1778, 588, 11396, 21947]

theorem plane454GenLeaf0005 (x : Fin 55 → Int)
    (hroot : plane454GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane454GenLeaf0005Refs i).resolveCoeff plane454GenOccSys j)
    (fun i => (plane454GenLeaf0005Refs i).resolveRhs plane454GenOccSys) plane454GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane454GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 10
  · exact hroot.hOcc 12
  · exact hroot.hOcc 18
  · exact hroot.hOcc 28
  · exact hroot.hOcc 30
  · exact hroot.hOcc 44
  · exact hroot.hOcc 51
  · exact hroot.hOcc 52
  · exact hroot.hOcc 53
  · exact hroot.hOcc 56
  · exact hroot.hOcc 62
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 66
  · exact hroot.hOcc 67
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 91
  · exact hroot.hOcc 96
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 107
  · exact hroot.hOcc 111
  · exact hroot.hOcc 118
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 133
  · exact hroot.hOcc 147
  · exact hroot.hOcc 152
  · exact hroot.hOcc 154
  · exact hroot.hOcc 158
  · exact hroot.hOcc 160
  · exact hroot.hOcc 163
  · exact hroot.hOcc 173
  · change (∑ j, (-1 : Int) * x j) ≤ -plane454GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (17 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (24 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (27 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (29 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (33 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (37 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (41 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (45 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (51 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (52 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (53 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (54 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (4 : Fin 55) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (16 : Fin 55) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
