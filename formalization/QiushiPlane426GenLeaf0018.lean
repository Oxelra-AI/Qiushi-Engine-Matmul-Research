import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0018Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 11, .occ 47, .occ 49, .occ 76, .occ 78, .occ 79, .occ 81, .occ 84, .occ 88, .occ 102, .occ 103, .occ 104, .occ 113, .occ 121, .occ 123, .occ 124, .occ 125, .occ 131, .occ 135, .occ 142, .occ 154, .occ 155, .occ 180, .occ 208, .occ 232, .occ 235, .occ 237, .occ 251, .occ 258, .occ 271, .occ 279, .occ 281, .occ 284, .occ 298, .occ 304, .occ 318, .sumGe, .nonneg 5, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 23, .nonneg 25, .nonneg 33, .nonneg 36, .nonneg 38, .nonneg 44, .nonneg 50, .nonneg 52, .branchLe 43 (0), .branchGe 14 (1), .branchLe 42 (0), .branchLe 18 (0), .branchLe 56 (0), .branchLe 11 (0), .branchLe 6 (0), .branchLe 51 (0), .branchLe 49 (0)]

def plane426GenLeaf0018Mult : Fin 59 → Nat := ![104617, 17801, 45892, 5168, 110562, 3572, 32463, 46416, 62942, 81853, 53119, 58353, 64065, 183249, 136715, 3955, 608, 65035, 118923, 41450, 55424, 64961, 6202, 10431, 111877, 35211, 1943, 3934, 67215, 25075, 36519, 46267, 31459, 52161, 64065, 25267, 41204, 278773, 30663, 216350, 453364, 28904, 38227, 35827, 71218, 9190, 8324, 28171, 221681, 103647, 237323, 377395, 180099, 278773, 198274, 276830, 31732, 274839, 241619]

theorem plane426GenLeaf0018 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_56 : x 56 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_51 : x 51 ≤ (0 : Int))
    (hUB_49 : x 49 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0018Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0018Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0018Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0018Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 11
  · exact hroot.hOcc 47
  · exact hroot.hOcc 49
  · exact hroot.hOcc 76
  · exact hroot.hOcc 78
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 84
  · exact hroot.hOcc 88
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 113
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 131
  · exact hroot.hOcc 135
  · exact hroot.hOcc 142
  · exact hroot.hOcc 154
  · exact hroot.hOcc 155
  · exact hroot.hOcc 180
  · exact hroot.hOcc 208
  · exact hroot.hOcc 232
  · exact hroot.hOcc 235
  · exact hroot.hOcc 237
  · exact hroot.hOcc 251
  · exact hroot.hOcc 258
  · exact hroot.hOcc 271
  · exact hroot.hOcc 279
  · exact hroot.hOcc 281
  · exact hroot.hOcc 284
  · exact hroot.hOcc 298
  · exact hroot.hOcc 304
  · exact hroot.hOcc 318
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (38 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (44 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (42 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (18 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (56 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_56
  · change (∑ k, (if k = (11 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (6 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (51 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_51
  · change (∑ k, (if k = (49 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_49

end QiushiMatmul
