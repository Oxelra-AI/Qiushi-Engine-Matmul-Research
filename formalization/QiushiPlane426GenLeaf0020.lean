import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0020Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 28, .occ 42, .occ 43, .occ 44, .occ 45, .occ 69, .occ 76, .occ 81, .occ 88, .occ 103, .occ 104, .occ 113, .occ 117, .occ 121, .occ 122, .occ 130, .occ 131, .occ 132, .occ 135, .occ 138, .occ 222, .occ 223, .occ 232, .occ 237, .occ 249, .occ 252, .occ 263, .occ 272, .occ 278, .occ 280, .occ 282, .occ 285, .occ 294, .occ 334, .occ 335, .sumGe, .nonneg 5, .nonneg 16, .nonneg 17, .nonneg 22, .nonneg 26, .nonneg 30, .nonneg 32, .nonneg 33, .nonneg 36, .nonneg 37, .nonneg 39, .nonneg 40, .nonneg 44, .nonneg 47, .branchLe 43 (0), .branchGe 14 (1), .branchLe 42 (0), .branchLe 18 (0), .branchLe 56 (0), .branchLe 11 (0), .branchLe 6 (0), .branchGe 51 (1)]

def plane426GenLeaf0020Mult : Fin 59 → Nat := ![91654, 7042, 55339, 82133, 17924, 62079, 11603, 31278, 41448, 5685, 86102, 16115, 35417, 121530, 12289, 37938, 18151, 43789, 4555, 681, 20283, 5738, 22731, 53716, 28387, 16905, 39332, 8290, 15289, 39790, 7030, 4030, 4714, 16612, 13957, 41082, 142504, 101866, 166715, 129473, 24779, 52753, 44515, 20148, 51045, 66701, 28914, 59752, 61168, 100029, 6169, 61901, 256110, 12953, 87465, 117602, 86579, 95737, 388179]

theorem plane426GenLeaf0020 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_51 : (1 : Int) ≤ x 51)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_56 : x 56 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0020Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0020Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0020Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0020Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 28
  · exact hroot.hOcc 42
  · exact hroot.hOcc 43
  · exact hroot.hOcc 44
  · exact hroot.hOcc 45
  · exact hroot.hOcc 69
  · exact hroot.hOcc 76
  · exact hroot.hOcc 81
  · exact hroot.hOcc 88
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 113
  · exact hroot.hOcc 117
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 222
  · exact hroot.hOcc 223
  · exact hroot.hOcc 232
  · exact hroot.hOcc 237
  · exact hroot.hOcc 249
  · exact hroot.hOcc 252
  · exact hroot.hOcc 263
  · exact hroot.hOcc 272
  · exact hroot.hOcc 278
  · exact hroot.hOcc 280
  · exact hroot.hOcc 282
  · exact hroot.hOcc 285
  · exact hroot.hOcc 294
  · exact hroot.hOcc 334
  · exact hroot.hOcc 335
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (22 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (30 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 30
  · change (∑ k, (if k = (32 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (37 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 37
  · change (∑ k, (if k = (39 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (40 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 40
  · change (∑ k, (if k = (44 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 44
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (42 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (18 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (56 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_56
  · change (∑ k, (if k = (11 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (6 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (51 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_51

end QiushiMatmul
