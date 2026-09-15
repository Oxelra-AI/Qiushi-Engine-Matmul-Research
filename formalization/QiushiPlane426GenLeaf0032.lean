import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0032Refs : Fin 59 → RowRef 340 58 := ![.occ 7, .occ 20, .occ 29, .occ 31, .occ 41, .occ 57, .occ 68, .occ 69, .occ 71, .occ 76, .occ 81, .occ 84, .occ 86, .occ 88, .occ 99, .occ 106, .occ 109, .occ 112, .occ 113, .occ 121, .occ 122, .occ 124, .occ 131, .occ 133, .occ 135, .occ 137, .occ 138, .occ 164, .occ 175, .occ 184, .occ 188, .occ 189, .occ 198, .occ 200, .occ 226, .occ 237, .occ 239, .occ 274, .occ 276, .occ 278, .occ 285, .occ 295, .occ 316, .occ 323, .occ 325, .occ 330, .sumGe, .nonneg 5, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 22, .nonneg 25, .nonneg 26, .nonneg 30, .nonneg 31, .branchGe 43 (1), .branchLe 34 (0), .branchLe 37 (0)]

def plane426GenLeaf0032Mult : Fin 59 → Nat := ![186219, 1038580, 349482, 200133, 346431, 345757, 74899, 141777, 153748, 209452, 58316, 475843, 89297, 52684, 117917, 247406, 369980, 133215, 146329, 48440, 75701, 205855, 80705, 273584, 691003, 110065, 458631, 53075, 451335, 183285, 283250, 8201, 18049, 24663, 128408, 28516, 282783, 34406, 91462, 46794, 296261, 389405, 331934, 166056, 81200, 79832, 1148296, 253429, 916914, 2383451, 45978, 249691, 540049, 124702, 42849, 34406, 5432975, 523609, 1065450]

theorem plane426GenLeaf0032 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_34 : x 34 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0032Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0032Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0032Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0032Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 7
  · exact hroot.hOcc 20
  · exact hroot.hOcc 29
  · exact hroot.hOcc 31
  · exact hroot.hOcc 41
  · exact hroot.hOcc 57
  · exact hroot.hOcc 68
  · exact hroot.hOcc 69
  · exact hroot.hOcc 71
  · exact hroot.hOcc 76
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 99
  · exact hroot.hOcc 106
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 164
  · exact hroot.hOcc 175
  · exact hroot.hOcc 184
  · exact hroot.hOcc 188
  · exact hroot.hOcc 189
  · exact hroot.hOcc 198
  · exact hroot.hOcc 200
  · exact hroot.hOcc 226
  · exact hroot.hOcc 237
  · exact hroot.hOcc 239
  · exact hroot.hOcc 274
  · exact hroot.hOcc 276
  · exact hroot.hOcc 278
  · exact hroot.hOcc 285
  · exact hroot.hOcc 295
  · exact hroot.hOcc 316
  · exact hroot.hOcc 323
  · exact hroot.hOcc 325
  · exact hroot.hOcc 330
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (22 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (30 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (31 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (43 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (34 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (37 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37

end QiushiMatmul
