import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0047Refs : Fin 43 → RowRef 1665 43 := ![.occ 121, .occ 128, .occ 133, .occ 140, .occ 145, .occ 150, .occ 174, .occ 178, .occ 336, .occ 381, .occ 433, .occ 699, .occ 1150, .occ 1158, .occ 1160, .occ 1205, .occ 1208, .occ 1284, .occ 1357, .occ 1389, .occ 1395, .occ 1397, .occ 1405, .occ 1472, .occ 1478, .occ 1580, .occ 1607, .occ 1615, .occ 1634, .sumGe, .nonneg 5, .nonneg 7, .nonneg 10, .nonneg 15, .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchGe 17 (1), .branchLe 18 (0), .branchGe 1 (1), .branchLe 38 (0), .branchGe 3 (1)]

def plane484GenLeaf0047Mult : Fin 43 → Nat := ![322, 294, 304, 344, 44, 156, 20, 52, 290, 22, 196, 154, 1, 31, 120, 54, 6, 6, 38, 24, 20, 18, 68, 37, 46, 28, 18, 159, 20, 410, 274, 68, 20, 482, 390, 290, 40, 88, 1212, 284, 1026, 410, 1300]

theorem plane484GenLeaf0047 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0047Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0047Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0047Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0047Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 128
  · exact hroot.hOcc 133
  · exact hroot.hOcc 140
  · exact hroot.hOcc 145
  · exact hroot.hOcc 150
  · exact hroot.hOcc 174
  · exact hroot.hOcc 178
  · exact hroot.hOcc 336
  · exact hroot.hOcc 381
  · exact hroot.hOcc 433
  · exact hroot.hOcc 699
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1284
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1389
  · exact hroot.hOcc 1395
  · exact hroot.hOcc 1397
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1634
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
