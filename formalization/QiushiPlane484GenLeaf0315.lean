import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0315Refs : Fin 42 → RowRef 1665 43 := ![.occ 120, .occ 124, .occ 126, .occ 132, .occ 137, .occ 139, .occ 141, .occ 584, .occ 726, .occ 770, .occ 837, .occ 1145, .occ 1168, .occ 1196, .occ 1214, .occ 1216, .occ 1233, .occ 1234, .occ 1254, .occ 1357, .occ 1384, .occ 1423, .occ 1433, .occ 1492, .occ 1524, .occ 1607, .occ 1650, .sumGe, .nonneg 7, .nonneg 9, .nonneg 25, .branchLe 15 (0), .branchGe 2 (1), .branchLe 23 (0), .branchGe 26 (1), .branchLe 14 (0), .branchLe 1 (0), .branchLe 22 (0), .branchLe 16 (0), .branchGe 0 (1), .branchLe 31 (0), .branchGe 10 (1)]

def plane484GenLeaf0315Mult : Fin 42 → Nat := ![44, 183, 174, 2, 119, 86, 80, 213, 36, 44, 69, 4, 193, 2, 4, 21, 25, 13, 35, 14, 5, 11, 15, 4, 6, 127, 20, 242, 244, 30, 187, 242, 244, 107, 772, 8, 132, 240, 2, 239, 228, 750]

theorem plane484GenLeaf0315 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0315Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0315Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0315Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0315Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 126
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 584
  · exact hroot.hOcc 726
  · exact hroot.hOcc 770
  · exact hroot.hOcc 837
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1254
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1423
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
