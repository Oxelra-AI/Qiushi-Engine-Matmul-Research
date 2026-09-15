import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0246Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 126, .occ 128, .occ 134, .occ 135, .occ 136, .occ 142, .occ 180, .occ 318, .occ 320, .occ 621, .occ 671, .occ 714, .occ 1065, .occ 1158, .occ 1174, .occ 1200, .occ 1220, .occ 1231, .occ 1278, .occ 1371, .occ 1426, .occ 1459, .occ 1470, .occ 1489, .occ 1564, .occ 1567, .occ 1615, .occ 1648, .sumGe, .nonneg 15, .nonneg 17, .nonneg 22, .nonneg 24, .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchGe 16 (1), .branchLe 13 (0), .branchLe 41 (0), .branchLe 4 (0), .branchGe 25 (1)]

def plane484GenLeaf0246Mult : Fin 44 → Nat := ![3641, 1847, 3639, 8083, 3951, 19477, 5630, 4250, 2809, 405, 666, 127, 4587, 121, 7998, 2777, 517, 1566, 2569, 6182, 1515, 3511, 2083, 4461, 2678, 6015, 3456, 2208, 1254, 21043, 8045, 1890, 21019, 3639, 16387, 15165, 7366, 15413, 17587, 45962, 18960, 21043, 14585, 43899]

theorem plane484GenLeaf0246 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0246Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0246Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0246Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0246Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 142
  · exact hroot.hOcc 180
  · exact hroot.hOcc 318
  · exact hroot.hOcc 320
  · exact hroot.hOcc 621
  · exact hroot.hOcc 671
  · exact hroot.hOcc 714
  · exact hroot.hOcc 1065
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1231
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1564
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1648
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
