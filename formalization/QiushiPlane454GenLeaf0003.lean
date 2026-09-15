import QiushiPlane454GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane454GenLeaf0003Refs : Fin 56 → RowRef 174 55 := ![.occ 8, .occ 18, .occ 30, .occ 31, .occ 42, .occ 44, .occ 61, .occ 69, .occ 70, .occ 80, .occ 81, .occ 89, .occ 90, .occ 91, .occ 97, .occ 98, .occ 109, .occ 112, .occ 114, .occ 115, .occ 116, .occ 120, .occ 121, .occ 122, .occ 123, .occ 128, .occ 130, .occ 135, .occ 138, .occ 147, .occ 148, .occ 151, .occ 152, .occ 154, .occ 157, .occ 158, .occ 161, .occ 162, .occ 163, .occ 168, .occ 172, .occ 173, .sumGe, .nonneg 18, .nonneg 29, .nonneg 37, .nonneg 38, .nonneg 41, .nonneg 44, .nonneg 48, .nonneg 51, .nonneg 52, .nonneg 53, .branchLe 2 (0), .branchGe 4 (1), .branchLe 5 (0)]

def plane454GenLeaf0003Mult : Fin 56 → Nat := ![616580, 1063952, 460152, 974244, 481784, 790656, 579104, 164604, 192728, 700076, 742120, 161416, 274616, 1022196, 656024, 16016, 128888, 216726, 3420, 281126, 311348, 116298, 368462, 516376, 86640, 215682, 352746, 804074, 134348, 385564, 153678, 154872, 451976, 1120430, 563666, 1015905, 440494, 481185, 298718, 637813, 433558, 550671, 4228528, 679072, 372124, 397748, 808564, 1066208, 61236, 820836, 637748, 29668, 176596, 3133048, 4823132, 4228528]

theorem plane454GenLeaf0003 (x : Fin 55 → Int)
    (hroot : plane454GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane454GenLeaf0003Refs i).resolveCoeff plane454GenOccSys j)
    (fun i => (plane454GenLeaf0003Refs i).resolveRhs plane454GenOccSys) plane454GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane454GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 8
  · exact hroot.hOcc 18
  · exact hroot.hOcc 30
  · exact hroot.hOcc 31
  · exact hroot.hOcc 42
  · exact hroot.hOcc 44
  · exact hroot.hOcc 61
  · exact hroot.hOcc 69
  · exact hroot.hOcc 70
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 97
  · exact hroot.hOcc 98
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 116
  · exact hroot.hOcc 120
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 147
  · exact hroot.hOcc 148
  · exact hroot.hOcc 151
  · exact hroot.hOcc 152
  · exact hroot.hOcc 154
  · exact hroot.hOcc 157
  · exact hroot.hOcc 158
  · exact hroot.hOcc 161
  · exact hroot.hOcc 162
  · exact hroot.hOcc 163
  · exact hroot.hOcc 168
  · exact hroot.hOcc 172
  · exact hroot.hOcc 173
  · change (∑ j, (-1 : Int) * x j) ≤ -plane454GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (29 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 29
  · change (∑ k, (if k = (37 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (38 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (41 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (44 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (48 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 48
  · change (∑ k, (if k = (51 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (52 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (53 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (2 : Fin 55) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (4 : Fin 55) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (5 : Fin 55) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5

end QiushiMatmul
