import QiushiPlane468GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane468GenLeaf0012Refs : Fin 63 → RowRef 253 62 := ![.occ 14, .occ 17, .occ 39, .occ 42, .occ 43, .occ 44, .occ 47, .occ 54, .occ 66, .occ 73, .occ 74, .occ 90, .occ 98, .occ 105, .occ 106, .occ 109, .occ 110, .occ 124, .occ 130, .occ 133, .occ 135, .occ 142, .occ 158, .occ 163, .occ 170, .occ 176, .occ 181, .occ 184, .occ 188, .occ 191, .occ 193, .occ 208, .occ 220, .occ 226, .occ 229, .occ 230, .occ 232, .occ 237, .occ 238, .occ 239, .occ 244, .occ 245, .occ 246, .sumGe, .nonneg 7, .nonneg 8, .nonneg 10, .nonneg 18, .nonneg 20, .nonneg 30, .nonneg 34, .nonneg 37, .nonneg 39, .nonneg 42, .nonneg 45, .nonneg 46, .nonneg 50, .nonneg 53, .nonneg 56, .nonneg 60, .branchGe 28 (1), .branchLe 36 (0), .branchGe 55 (1)]

def plane468GenLeaf0012Mult : Fin 63 → Nat := ![10884, 232948, 31916, 291454, 159888, 155552, 150850, 500746, 147356, 162012, 130210, 84042, 8514, 351370, 41910, 314312, 84142, 41072, 147654, 31450, 16596, 344684, 9002, 45088, 136338, 91704, 35192, 45886, 102294, 42444, 49862, 88704, 4640, 41698, 126270, 88200, 199932, 55780, 94495, 112541, 29391, 48791, 41072, 646614, 215512, 234338, 225806, 19084, 218538, 13410, 247612, 287590, 91772, 416942, 107132, 94418, 207664, 294466, 107174, 187324, 1266724, 408934, 1558112]

theorem plane468GenLeaf0012 (x : Fin 62 → Int)
    (hroot : plane468GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_55 : (1 : Int) ≤ x 55)
    (hUB_36 : x 36 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane468GenLeaf0012Refs i).resolveCoeff plane468GenOccSys j)
    (fun i => (plane468GenLeaf0012Refs i).resolveRhs plane468GenOccSys) plane468GenLeaf0012Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane468GenLeaf0012Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 14
  · exact hroot.hOcc 17
  · exact hroot.hOcc 39
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 47
  · exact hroot.hOcc 54
  · exact hroot.hOcc 66
  · exact hroot.hOcc 73
  · exact hroot.hOcc 74
  · exact hroot.hOcc 90
  · exact hroot.hOcc 98
  · exact hroot.hOcc 105
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 110
  · exact hroot.hOcc 124
  · exact hroot.hOcc 130
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 142
  · exact hroot.hOcc 158
  · exact hroot.hOcc 163
  · exact hroot.hOcc 170
  · exact hroot.hOcc 176
  · exact hroot.hOcc 181
  · exact hroot.hOcc 184
  · exact hroot.hOcc 188
  · exact hroot.hOcc 191
  · exact hroot.hOcc 193
  · exact hroot.hOcc 208
  · exact hroot.hOcc 220
  · exact hroot.hOcc 226
  · exact hroot.hOcc 229
  · exact hroot.hOcc 230
  · exact hroot.hOcc 232
  · exact hroot.hOcc 237
  · exact hroot.hOcc 238
  · exact hroot.hOcc 239
  · exact hroot.hOcc 244
  · exact hroot.hOcc 245
  · exact hroot.hOcc 246
  · change (∑ j, (-1 : Int) * x j) ≤ -plane468GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (8 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (10 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (18 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (20 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (30 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (34 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (37 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (39 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (42 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 42
  · change (∑ k, (if k = (45 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 45
  · change (∑ k, (if k = (46 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (50 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (53 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 53
  · change (∑ k, (if k = (56 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 56
  · change (∑ k, (if k = (60 : Fin 62) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 60
  · change (∑ k, (if k = (28 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (36 : Fin 62) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (55 : Fin 62) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_55

end QiushiMatmul
