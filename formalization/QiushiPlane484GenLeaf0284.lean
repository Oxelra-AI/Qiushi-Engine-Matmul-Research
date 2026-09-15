import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0284Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 126, .occ 128, .occ 130, .occ 136, .occ 177, .occ 261, .occ 290, .occ 332, .occ 551, .occ 559, .occ 681, .occ 707, .occ 1136, .occ 1140, .occ 1180, .occ 1190, .occ 1196, .occ 1205, .occ 1255, .occ 1273, .occ 1283, .occ 1357, .occ 1471, .occ 1486, .occ 1491, .occ 1502, .occ 1567, .occ 1580, .occ 1625, .occ 1645, .sumGe, .nonneg 7, .nonneg 13, .nonneg 22, .branchLe 15 (0), .branchGe 2 (1), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchGe 37 (1), .branchGe 32 (1), .branchGe 10 (1)]

def plane484GenLeaf0284Mult : Fin 44 → Nat := ![601, 2480, 8445, 9545, 1684, 828, 416, 14997, 1266, 10608, 18384, 3930, 1266, 742, 4266, 4102, 586, 8880, 5936, 16862, 1668, 2272, 1158, 6830, 20656, 264, 3418, 3940, 1672, 42, 2008, 27750, 5934, 1852, 2958, 19806, 16850, 26592, 17412, 53960, 27008, 27172, 64418, 94000]

theorem plane484GenLeaf0284 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0284Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0284Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0284Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0284Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 136
  · exact hroot.hOcc 177
  · exact hroot.hOcc 261
  · exact hroot.hOcc 290
  · exact hroot.hOcc 332
  · exact hroot.hOcc 551
  · exact hroot.hOcc 559
  · exact hroot.hOcc 681
  · exact hroot.hOcc 707
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1180
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1255
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1283
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1502
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1645
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
