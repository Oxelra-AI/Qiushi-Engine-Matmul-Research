import QiushiPlane485GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane485GenLeaf0009Refs : Fin 42 → RowRef 421 41 := ![.occ 87, .occ 93, .occ 134, .occ 135, .occ 136, .occ 138, .occ 155, .occ 164, .occ 179, .occ 184, .occ 213, .occ 218, .occ 224, .occ 228, .occ 237, .occ 246, .occ 262, .occ 270, .occ 276, .occ 295, .occ 296, .occ 300, .occ 302, .occ 305, .occ 322, .occ 332, .occ 341, .occ 359, .occ 393, .occ 401, .occ 414, .sumGe, .nonneg 0, .nonneg 12, .branchLe 28 (0), .branchLe 21 (0), .branchLe 14 (0), .branchLe 11 (0), .branchGe 39 (1), .branchGe 29 (1), .branchLe 25 (0), .branchGe 6 (1)]

def plane485GenLeaf0009Mult : Fin 42 → Nat := ![7311, 3689, 141, 10552, 13172, 4910, 3406, 8402, 2127, 1009, 7231, 8130, 16908, 5807, 213, 9892, 1438, 11927, 4887, 1398, 2145, 4885, 2044, 28, 398, 1425, 3149, 1220, 7325, 6931, 1307, 25059, 1604, 11622, 15622, 6753, 22006, 1335, 30742, 50885, 12018, 46563]

theorem plane485GenLeaf0009 (x : Fin 41 → Int)
    (hroot : plane485GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane485GenLeaf0009Refs i).resolveCoeff plane485GenOccSys j)
    (fun i => (plane485GenLeaf0009Refs i).resolveRhs plane485GenOccSys) plane485GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane485GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 87
  · exact hroot.hOcc 93
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 155
  · exact hroot.hOcc 164
  · exact hroot.hOcc 179
  · exact hroot.hOcc 184
  · exact hroot.hOcc 213
  · exact hroot.hOcc 218
  · exact hroot.hOcc 224
  · exact hroot.hOcc 228
  · exact hroot.hOcc 237
  · exact hroot.hOcc 246
  · exact hroot.hOcc 262
  · exact hroot.hOcc 270
  · exact hroot.hOcc 276
  · exact hroot.hOcc 295
  · exact hroot.hOcc 296
  · exact hroot.hOcc 300
  · exact hroot.hOcc 302
  · exact hroot.hOcc 305
  · exact hroot.hOcc 322
  · exact hroot.hOcc 332
  · exact hroot.hOcc 341
  · exact hroot.hOcc 359
  · exact hroot.hOcc 393
  · exact hroot.hOcc 401
  · exact hroot.hOcc 414
  · change (∑ j, (-1 : Int) * x j) ≤ -plane485GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (12 : Fin 41) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (28 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (21 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (14 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (11 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (39 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (29 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (25 : Fin 41) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (6 : Fin 41) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
