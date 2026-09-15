import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0539Refs : Fin 41 → RowRef 1665 43 := ![.occ 131, .occ 138, .occ 196, .occ 212, .occ 224, .occ 244, .occ 295, .occ 427, .occ 471, .occ 599, .occ 713, .occ 908, .occ 1170, .occ 1183, .occ 1227, .occ 1260, .occ 1264, .occ 1288, .occ 1310, .occ 1317, .occ 1339, .occ 1343, .occ 1367, .occ 1446, .occ 1450, .occ 1488, .occ 1629, .occ 1642, .sumGe, .nonneg 0, .nonneg 23, .nonneg 24, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchLe 1 (0), .branchGe 19 (1), .branchLe 6 (0), .branchGe 20 (1)]

def plane484GenLeaf0539Mult : Fin 41 → Nat := ![223, 101, 28, 68, 52, 58, 223, 29, 2, 64, 57, 44, 108, 7, 99, 29, 51, 37, 32, 3, 15, 21, 19, 27, 59, 44, 17, 71, 223, 108, 368, 108, 611, 660, 101, 51, 896, 206, 462, 223, 368]

theorem plane484GenLeaf0539 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0539Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0539Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0539Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0539Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 131
  · exact hroot.hOcc 138
  · exact hroot.hOcc 196
  · exact hroot.hOcc 212
  · exact hroot.hOcc 224
  · exact hroot.hOcc 244
  · exact hroot.hOcc 295
  · exact hroot.hOcc 427
  · exact hroot.hOcc 471
  · exact hroot.hOcc 599
  · exact hroot.hOcc 713
  · exact hroot.hOcc 908
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1227
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1288
  · exact hroot.hOcc 1310
  · exact hroot.hOcc 1317
  · exact hroot.hOcc 1339
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1446
  · exact hroot.hOcc 1450
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1642
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
