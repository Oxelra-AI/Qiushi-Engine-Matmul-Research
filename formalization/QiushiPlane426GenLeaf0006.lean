import QiushiPlane426GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane426GenLeaf0006Refs : Fin 59 → RowRef 340 58 := ![.occ 5, .occ 14, .occ 23, .occ 26, .occ 40, .occ 44, .occ 46, .occ 71, .occ 76, .occ 79, .occ 81, .occ 86, .occ 88, .occ 98, .occ 99, .occ 103, .occ 104, .occ 116, .occ 117, .occ 122, .occ 123, .occ 124, .occ 132, .occ 140, .occ 142, .occ 143, .occ 144, .occ 146, .occ 164, .occ 181, .occ 186, .occ 200, .occ 205, .occ 206, .occ 227, .occ 241, .occ 278, .occ 280, .occ 290, .occ 291, .occ 293, .occ 310, .occ 325, .occ 327, .occ 333, .sumGe, .nonneg 8, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 26, .nonneg 47, .branchLe 43 (0), .branchLe 14 (0), .branchGe 1 (1), .branchLe 35 (0), .branchLe 4 (0), .branchLe 10 (0), .branchLe 34 (0)]

def plane426GenLeaf0006Mult : Fin 59 → Nat := ![212334, 200918, 81526, 178454, 13199, 180832, 210189, 217295, 74410, 261558, 7733, 264767, 490200, 191666, 173747, 218017, 424484, 274838, 147099, 172817, 274642, 188441, 299419, 56286, 79504, 56917, 403061, 181230, 229506, 149479, 168560, 109320, 200068, 24168, 267749, 129223, 140809, 213648, 76068, 97817, 153370, 32249, 141699, 18095, 105525, 1132056, 265212, 974537, 1239481, 307183, 249887, 11813, 984738, 617508, 1136323, 598574, 899116, 710785, 1037893]

theorem plane426GenLeaf0006 (x : Fin 58 → Int)
    (hroot : plane426GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hUB_43 : x 43 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane426GenLeaf0006Refs i).resolveCoeff plane426GenOccSys j)
    (fun i => (plane426GenLeaf0006Refs i).resolveRhs plane426GenOccSys) plane426GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane426GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 5
  · exact hroot.hOcc 14
  · exact hroot.hOcc 23
  · exact hroot.hOcc 26
  · exact hroot.hOcc 40
  · exact hroot.hOcc 44
  · exact hroot.hOcc 46
  · exact hroot.hOcc 71
  · exact hroot.hOcc 76
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 86
  · exact hroot.hOcc 88
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 104
  · exact hroot.hOcc 116
  · exact hroot.hOcc 117
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 132
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 144
  · exact hroot.hOcc 146
  · exact hroot.hOcc 164
  · exact hroot.hOcc 181
  · exact hroot.hOcc 186
  · exact hroot.hOcc 200
  · exact hroot.hOcc 205
  · exact hroot.hOcc 206
  · exact hroot.hOcc 227
  · exact hroot.hOcc 241
  · exact hroot.hOcc 278
  · exact hroot.hOcc 280
  · exact hroot.hOcc 290
  · exact hroot.hOcc 291
  · exact hroot.hOcc 293
  · exact hroot.hOcc 310
  · exact hroot.hOcc 325
  · exact hroot.hOcc 327
  · exact hroot.hOcc 333
  · change (∑ j, (-1 : Int) * x j) ≤ -plane426GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (8 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 8
  · change (∑ k, (if k = (16 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (26 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (47 : Fin 58) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 47
  · change (∑ k, (if k = (43 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (14 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 58) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (35 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (4 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (10 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (34 : Fin 58) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34

end QiushiMatmul
