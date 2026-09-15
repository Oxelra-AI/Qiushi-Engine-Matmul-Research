import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0016Refs : Fin 59 → RowRef 340 58 := ![.occ 35, .occ 47, .occ 52, .occ 61, .occ 74, .occ 86, .occ 88, .occ 89, .occ 99, .occ 100, .occ 104, .occ 109, .occ 116, .occ 122, .occ 123, .occ 124, .occ 140, .occ 144, .occ 145, .occ 164, .occ 200, .occ 208, .occ 210, .occ 225, .occ 242, .occ 254, .occ 261, .occ 268, .occ 280, .occ 282, .occ 284, .occ 298, .occ 307, .occ 312, .occ 313, .occ 314, .occ 318, .occ 333, .sumGe, .nonneg 6, .nonneg 16, .nonneg 17, .nonneg 18, .nonneg 19, .nonneg 24, .nonneg 25, .nonneg 26, .nonneg 28, .nonneg 32, .nonneg 38, .nonneg 47, .nonneg 50, .nonneg 52, .branchLe 43 (0), .branchLe 14 (0), .branchGe 1 (1), .branchGe 35 (1), .branchLe 13 (0), .branchGe 20 (1)]

def plane426GenLeaf0016Mult : Fin 59 → Nat := ![3305, 7324, 7614, 7368, 2891, 20150, 4128, 3927, 1495, 2824, 7429, 1808, 8407, 2489, 2294, 12408, 6138, 5804, 1869, 3896, 5404, 3543, 2074, 10413, 4655, 34, 333, 956, 366, 6721, 4361, 10264, 3463, 3977, 1021, 2009, 58, 6201, 24278, 333, 16679, 18782, 6285, 23675, 2132, 9868, 20571, 25410, 3628, 1394, 10905, 6329, 4413, 23322, 22137, 26592, 56581, 17711, 33758]

theorem plane426GenLeaf0016 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0016Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0016Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0016Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0016Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 35
  · exact hroot.hOcc 47
  · exact hroot.hOcc 52
  · exact hroot.hOcc 61
  · exact hroot.hOcc 74
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 89
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 109
  · exact hroot.hOcc 116
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 140
  · exact hroot.hOcc 144
  · exact hroot.hOcc 145
  · exact hroot.hOcc 164
  · exact hroot.hOcc 200
  · exact hroot.hOcc 208
  · exact hroot.hOcc 210
  · exact hroot.hOcc 225
  · exact hroot.hOcc 242
  · exact hroot.hOcc 254
  · exact hroot.hOcc 261
  · exact hroot.hOcc 268
  · exact hroot.hOcc 280
  · exact hroot.hOcc 282
  · exact hroot.hOcc 284
  · exact hroot.hOcc 298
  · exact hroot.hOcc 307
  · exact hroot.hOcc 312
  · exact hroot.hOcc 313
  · exact hroot.hOcc 314
  · exact hroot.hOcc 318
  · exact hroot.hOcc 333
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (18 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (25 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (32 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (38 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 38
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (52 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 52
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (35 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (13 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (20 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
