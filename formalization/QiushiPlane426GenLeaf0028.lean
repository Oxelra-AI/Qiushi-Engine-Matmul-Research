import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0028Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 8, .occ 48, .occ 53, .occ 60, .occ 66, .occ 76, .occ 81, .occ 85, .occ 86, .occ 88, .occ 96, .occ 102, .occ 103, .occ 117, .occ 121, .occ 123, .occ 124, .occ 131, .occ 135, .occ 140, .occ 141, .occ 144, .occ 174, .occ 190, .occ 219, .occ 235, .occ 243, .occ 259, .occ 269, .occ 280, .occ 294, .occ 298, .occ 305, .occ 317, .occ 318, .occ 322, .occ 325, .occ 335, .sumGe, .nonneg 5, .nonneg 16, .nonneg 17, .nonneg 23, .nonneg 24, .nonneg 26, .nonneg 28, .nonneg 36, .nonneg 46, .nonneg 47, .nonneg 50, .nonneg 57, .branchLe 43 (0), .branchGe 14 (1), .branchLe 42 (0), .branchGe 18 (1), .branchLe 49 (0), .branchGe 27 (1), .branchGe 37 (1)]

def plane426GenLeaf0028Mult : Fin 59 → Nat := ![5532, 12285, 3862, 10970, 3627, 1496, 922, 1273, 1380, 7881, 4200, 2420, 1979, 4495, 11251, 9948, 520, 2295, 3616, 8977, 705, 412, 2287, 2419, 1585, 2727, 3249, 1618, 4391, 1822, 3751, 4312, 4652, 2736, 9745, 1456, 1054, 2918, 1752, 18369, 11339, 11117, 14359, 8831, 481, 2800, 2336, 4805, 9604, 8951, 3288, 9192, 3984, 16938, 10447, 35162, 8451, 24033, 47068]

theorem plane426GenLeaf0028 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_49 : x 49 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0028Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0028Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0028Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0028Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 8
  · exact hroot.hOcc 48
  · exact hroot.hOcc 53
  · exact hroot.hOcc 60
  · exact hroot.hOcc 66
  · exact hroot.hOcc 76
  · exact hroot.hOcc 81
  · exact hroot.hOcc 85
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 96
  · exact hroot.hOcc 102
  · exact hroot.hOcc 103
  · exact hroot.hOcc 117
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 131
  · exact hroot.hOcc 135
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 144
  · exact hroot.hOcc 174
  · exact hroot.hOcc 190
  · exact hroot.hOcc 219
  · exact hroot.hOcc 235
  · exact hroot.hOcc 243
  · exact hroot.hOcc 259
  · exact hroot.hOcc 269
  · exact hroot.hOcc 280
  · exact hroot.hOcc 294
  · exact hroot.hOcc 298
  · exact hroot.hOcc 305
  · exact hroot.hOcc 317
  · exact hroot.hOcc 318
  · exact hroot.hOcc 322
  · exact hroot.hOcc 325
  · exact hroot.hOcc 335
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (23 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (46 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (57 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 57
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (42 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (18 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (49 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_49
  · change (∑ k, (if k = (27 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (37 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
