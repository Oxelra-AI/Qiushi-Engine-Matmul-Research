import QiushiPlane454GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane454GenLeaf0006Refs : Fin 56 → RowRef 174 55 := ![.occ 9, .occ 10, .occ 16, .occ 21, .occ 24, .occ 28, .occ 34, .occ 37, .occ 40, .occ 46, .occ 55, .occ 57, .occ 59, .occ 61, .occ 62, .occ 65, .occ 67, .occ 69, .occ 74, .occ 75, .occ 77, .occ 81, .occ 83, .occ 86, .occ 89, .occ 90, .occ 91, .occ 92, .occ 99, .occ 101, .occ 105, .occ 107, .occ 113, .occ 115, .occ 122, .occ 125, .occ 126, .occ 130, .occ 133, .occ 134, .occ 135, .occ 153, .occ 156, .occ 164, .occ 166, .occ 167, .sumGe, .nonneg 0, .nonneg 15, .nonneg 19, .nonneg 24, .nonneg 27, .nonneg 33, .nonneg 41, .nonneg 54, .branchGe 2 (1)]

def plane454GenLeaf0006Mult : Fin 56 → Nat := ![166355, 57101, 159372, 244983, 129304, 86439, 347395, 312392, 145183, 19872, 300, 189315, 562253, 302679, 292497, 48077, 52706, 102469, 49269, 10210, 23110, 180937, 41542, 250099, 138720, 191769, 28597, 18159, 279154, 124398, 37828, 64862, 119436, 99988, 277265, 105114, 242986, 7668, 3585, 65086, 32904, 127744, 36792, 4453, 174219, 21651, 680045, 7668, 43092, 99482, 146346, 234462, 243714, 50000, 186820, 3128632]

theorem plane454GenLeaf0006 (x : Fin 55 → Int)
    (hroot : plane454GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane454GenLeaf0006Refs i).resolveCoeff plane454GenOccSys j)
    (fun i => (plane454GenLeaf0006Refs i).resolveRhs plane454GenOccSys) plane454GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane454GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 9
  · exact hroot.hOcc 10
  · exact hroot.hOcc 16
  · exact hroot.hOcc 21
  · exact hroot.hOcc 24
  · exact hroot.hOcc 28
  · exact hroot.hOcc 34
  · exact hroot.hOcc 37
  · exact hroot.hOcc 40
  · exact hroot.hOcc 46
  · exact hroot.hOcc 55
  · exact hroot.hOcc 57
  · exact hroot.hOcc 59
  · exact hroot.hOcc 61
  · exact hroot.hOcc 62
  · exact hroot.hOcc 65
  · exact hroot.hOcc 67
  · exact hroot.hOcc 69
  · exact hroot.hOcc 74
  · exact hroot.hOcc 75
  · exact hroot.hOcc 77
  · exact hroot.hOcc 81
  · exact hroot.hOcc 83
  · exact hroot.hOcc 86
  · exact hroot.hOcc 89
  · exact hroot.hOcc 90
  · exact hroot.hOcc 91
  · exact hroot.hOcc 92
  · exact hroot.hOcc 99
  · exact hroot.hOcc 101
  · exact hroot.hOcc 105
  · exact hroot.hOcc 107
  · exact hroot.hOcc 113
  · exact hroot.hOcc 115
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 153
  · exact hroot.hOcc 156
  · exact hroot.hOcc 164
  · exact hroot.hOcc 166
  · exact hroot.hOcc 167
  · change (∑ j, (-1 : Int) * x j) ≤ -plane454GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (15 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (19 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (24 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (27 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 27
  · change (∑ k, (if k = (33 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (41 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (54 : Fin 55) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 54
  · change (∑ k, (if k = (2 : Fin 55) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2

end QiushiMatmul
