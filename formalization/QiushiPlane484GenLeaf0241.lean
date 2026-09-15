import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0241Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 123, .occ 126, .occ 129, .occ 164, .occ 362, .occ 861, .occ 1145, .occ 1146, .occ 1150, .occ 1172, .occ 1187, .occ 1188, .occ 1196, .occ 1213, .occ 1220, .occ 1274, .occ 1325, .occ 1329, .occ 1357, .occ 1458, .occ 1470, .occ 1472, .occ 1477, .occ 1483, .occ 1491, .occ 1580, .occ 1609, .occ 1644, .occ 1645, .sumGe, .nonneg 11, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchLe 16 (0), .branchGe 31 (1), .branchLe 20 (0), .branchGe 30 (1), .branchGe 6 (1)]

def plane484GenLeaf0241Mult : Fin 44 → Nat := ![80402, 17818, 26756, 30473, 4608, 58548, 46424, 32998, 7304, 95746, 9310, 35134, 1243, 4294, 3845, 16251, 97259, 6358, 3733, 8045, 15643, 11550, 608, 6036, 21731, 88913, 1352, 36723, 33465, 6340, 181204, 9248, 148157, 94792, 16064, 49108, 172548, 92291, 111016, 136189, 223960, 144550, 255923, 461094]

theorem plane484GenLeaf0241 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0241Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0241Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0241Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0241Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 129
  · exact hroot.hOcc 164
  · exact hroot.hOcc 362
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1274
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1329
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1645
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
