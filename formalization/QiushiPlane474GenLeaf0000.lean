import QiushiPlane474GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane474GenLeaf0000Refs : Fin 61 → RowRef 146 60 := ![.occ 5, .occ 6, .occ 12, .occ 20, .occ 23, .occ 25, .occ 29, .occ 33, .occ 35, .occ 39, .occ 42, .occ 44, .occ 45, .occ 50, .occ 51, .occ 53, .occ 57, .occ 63, .occ 64, .occ 65, .occ 69, .occ 75, .occ 76, .occ 77, .occ 78, .occ 79, .occ 80, .occ 81, .occ 82, .occ 84, .occ 95, .occ 97, .occ 99, .occ 101, .occ 103, .occ 108, .occ 110, .occ 111, .occ 112, .occ 121, .occ 127, .occ 131, .occ 134, .occ 136, .occ 137, .occ 138, .occ 142, .occ 144, .sumGe, .nonneg 6, .nonneg 9, .nonneg 17, .nonneg 38, .nonneg 41, .nonneg 46, .nonneg 51, .nonneg 52, .branchLe 44 (0), .branchLe 43 (0), .branchLe 22 (0), .branchLe 37 (0)]

def plane474GenLeaf0000Mult : Fin 61 → Nat := ![143231007, 109883676, 32998153, 21250531, 81147881, 16334523, 79345599, 83678187, 91286699, 34055339, 35052045, 74110415, 46184642, 283676025, 149534785, 316556506, 7854384, 73442093, 268125164, 45454442, 236606244, 16451311, 74417850, 221855223, 233085675, 83821824, 62238560, 14641684, 27573429, 23075722, 23524860, 155719604, 55316588, 192947355, 138496431, 76568849, 99002259, 100573745, 94166062, 29115096, 171567366, 160380711, 46747473, 64489525, 35211646, 97567687, 31377520, 50892990, 763724315, 275635, 44106142, 112679274, 50369527, 14366216, 66485912, 17436574, 562711167, 646242159, 347389499, 212511746, 590401154]

theorem plane474GenLeaf0000 (x : Fin 60 → Int)
    (hroot : plane474GenOccSys.RootHolds x)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane474GenLeaf0000Refs i).resolveCoeff plane474GenOccSys j)
    (fun i => (plane474GenLeaf0000Refs i).resolveRhs plane474GenOccSys) plane474GenLeaf0000Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane474GenLeaf0000Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 6
  · exact hroot.hOcc 12
  · exact hroot.hOcc 20
  · exact hroot.hOcc 23
  · exact hroot.hOcc 25
  · exact hroot.hOcc 29
  · exact hroot.hOcc 33
  · exact hroot.hOcc 35
  · exact hroot.hOcc 39
  · exact hroot.hOcc 42
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 50
  · exact hroot.hOcc 51
  · exact hroot.hOcc 53
  · exact hroot.hOcc 57
  · exact hroot.hOcc 63
  · exact hroot.hOcc 64
  · exact hroot.hOcc 65
  · exact hroot.hOcc 69
  · exact hroot.hOcc 75
  · exact hroot.hOcc 76
  · exact hroot.hOcc 77
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 80
  · exact hroot.hOcc 81
  · exact hroot.hOcc 82
  · exact hroot.hOcc 84
  · exact hroot.hOcc 95
  · exact hroot.hOcc 97
  · exact hroot.hOcc 99
  · exact hroot.hOcc 101
  · exact hroot.hOcc 103
  · exact hroot.hOcc 108
  · exact hroot.hOcc 110
  · exact hroot.hOcc 111
  · exact hroot.hOcc 112
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 131
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · change (∑ j, (-1 : Int) * x j) ≤ -plane474GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (9 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (17 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (38 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (41 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 41
  · change (∑ k, (if k = (46 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (51 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 51
  · change (∑ k, (if k = (52 : Fin 60) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (44 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (43 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (22 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (37 : Fin 60) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37

end QiushiMatmul
