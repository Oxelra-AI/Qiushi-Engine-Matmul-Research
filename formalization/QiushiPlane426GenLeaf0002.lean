import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0002Refs : Fin 59 → RowRef 340 58 := ![.occ 21, .occ 36, .occ 47, .occ 52, .occ 68, .occ 74, .occ 76, .occ 84, .occ 86, .occ 88, .occ 89, .occ 105, .occ 109, .occ 116, .occ 117, .occ 122, .occ 124, .occ 126, .occ 138, .occ 155, .occ 171, .occ 178, .occ 182, .occ 187, .occ 192, .occ 200, .occ 205, .occ 218, .occ 249, .occ 260, .occ 261, .occ 268, .occ 272, .occ 281, .occ 282, .occ 298, .occ 300, .occ 306, .occ 322, .occ 325, .occ 328, .occ 330, .occ 335, .sumGe, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 25, .nonneg 32, .nonneg 33, .nonneg 36, .nonneg 46, .branchLe 43 (0), .branchLe 14 (0), .branchLe 1 (0), .branchLe 13 (0), .branchLe 37 (0), .branchGe 21 (1), .branchGe 35 (1)]

def plane426GenLeaf0002Mult : Fin 59 → Nat := ![5756452, 177996, 1187892, 185884, 1457236, 27916, 1753996, 1754208, 1470880, 388700, 3408028, 2500520, 4809040, 918548, 344004, 1525284, 3265508, 905488, 1150408, 1024708, 1809992, 646108, 3357288, 1470880, 3170632, 306270, 371082, 1498796, 407336, 1086938, 1327064, 1037232, 1305052, 807772, 2629418, 2821226, 3347860, 1316734, 1535009, 2834973, 3536312, 3067331, 2083655, 14528160, 3356892, 5553692, 2192928, 932192, 1401492, 723780, 378600, 7444552, 2489480, 2145748, 12668580, 6073220, 14184156, 15244500, 31830592]

theorem plane426GenLeaf0002 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0002Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0002Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0002Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0002Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 21
  · exact hroot.hOcc 36
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 68
  · exact hroot.hOcc 74
  · exact hroot.hOcc 76
  · exact hroot.hOcc 84
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 105
  · exact hroot.hOcc 109
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 138
  · exact hroot.hOcc 155
  · exact hroot.hOcc 171
  · exact hroot.hOcc 178
  · exact hroot.hOcc 182
  · exact hroot.hOcc 187
  · exact hroot.hOcc 192
  · exact hroot.hOcc 200
  · exact hroot.hOcc 205
  · exact hroot.hOcc 218
  · exact hroot.hOcc 249
  · exact hroot.hOcc 260
  · exact hroot.hOcc 261
  · exact hroot.hOcc 268
  · exact hroot.hOcc 272
  · exact hroot.hOcc 281
  · exact hroot.hOcc 282
  · exact hroot.hOcc 298
  · exact hroot.hOcc 300
  · exact hroot.hOcc 306
  · exact hroot.hOcc 322
  · exact hroot.hOcc 325
  · exact hroot.hOcc 328
  · exact hroot.hOcc 330
  · exact hroot.hOcc 335
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (32 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (46 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (13 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (21 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (35 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35

end QiushiMatmul
