import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0027Refs : Fin 59 → RowRef 340 58 := ![.occ 12, .occ 30, .occ 60, .occ 76, .occ 81, .occ 86, .occ 88, .occ 103, .occ 104, .occ 107, .occ 113, .occ 121, .occ 122, .occ 126, .occ 131, .occ 132, .occ 135, .occ 140, .occ 142, .occ 143, .occ 190, .occ 201, .occ 205, .occ 213, .occ 219, .occ 237, .occ 249, .occ 257, .occ 258, .occ 275, .occ 289, .occ 298, .occ 305, .occ 322, .occ 325, .occ 328, .occ 335, .sumGe, .nonneg 4, .nonneg 5, .nonneg 6, .nonneg 8, .nonneg 16, .nonneg 17, .nonneg 28, .nonneg 32, .nonneg 33, .nonneg 36, .nonneg 39, .nonneg 43, .nonneg 46, .nonneg 50, .nonneg 55, .branchGe 14 (1), .branchLe 42 (0), .branchGe 18 (1), .branchLe 49 (0), .branchGe 27 (1), .branchLe 37 (0)]

def plane426GenLeaf0027Mult : Fin 59 → Nat := ![13770, 17572, 5774, 7900, 5295, 13499, 13062, 651, 5769, 1971, 9790, 2342, 6118, 11183, 7154, 1240, 23663, 7096, 4102, 100, 1728, 1534, 607, 7926, 10077, 2953, 1562, 3260, 272, 7956, 2851, 1800, 8968, 11828, 4346, 10962, 3175, 36598, 9934, 18587, 6944, 28609, 41598, 43601, 5865, 2415, 4020, 10506, 10306, 20385, 22032, 8645, 6507, 24022, 19610, 43656, 32252, 84516, 34256]

theorem plane426GenLeaf0027 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_49 : x 49 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0027Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0027Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0027Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0027Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 12
  · exact hroot.hOcc 30
  · exact hroot.hOcc 60
  · exact hroot.hOcc 76
  · exact hroot.hOcc 81
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 107
  · exact hroot.hOcc 113
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 126
  · exact hroot.hOcc 131
  · exact hroot.hOcc 132
  · exact hroot.hOcc 135
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 190
  · exact hroot.hOcc 201
  · exact hroot.hOcc 205
  · exact hroot.hOcc 213
  · exact hroot.hOcc 219
  · exact hroot.hOcc 237
  · exact hroot.hOcc 249
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 275
  · exact hroot.hOcc 289
  · exact hroot.hOcc 298
  · exact hroot.hOcc 305
  · exact hroot.hOcc 322
  · exact hroot.hOcc 325
  · exact hroot.hOcc 328
  · exact hroot.hOcc 335
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (5 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (6 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (8 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (28 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 28
  · change (∑ k, (if k = (32 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 32
  · change (∑ k, (if k = (33 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 33
  · change (∑ k, (if k = (36 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 36
  · change (∑ k, (if k = (39 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (43 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 43
  · change (∑ k, (if k = (46 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 46
  · change (∑ k, (if k = (50 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 50
  · change (∑ k, (if k = (55 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 55
  · change (∑ k, (if k = (14 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (42 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (18 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (49 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_49
  · change (∑ k, (if k = (27 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (37 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37

end QiushiMatmul
