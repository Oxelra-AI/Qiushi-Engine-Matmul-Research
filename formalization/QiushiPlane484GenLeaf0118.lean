import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0118Refs : Fin 37 → RowRef 1665 43 := ![.occ 119, .occ 127, .occ 130, .occ 132, .occ 137, .occ 139, .occ 140, .occ 142, .occ 209, .occ 423, .occ 428, .occ 805, .occ 1079, .occ 1084, .occ 1087, .occ 1145, .occ 1238, .occ 1248, .occ 1289, .occ 1325, .occ 1336, .occ 1437, .occ 1503, .occ 1508, .occ 1573, .occ 1654, .sumGe, .nonneg 1, .nonneg 2, .nonneg 16, .nonneg 18, .branchLe 29 (0), .branchGe 4 (1), .branchGe 36 (1), .branchGe 26 (1), .branchGe 21 (1), .branchGe 24 (1)]

def plane484GenLeaf0118Mult : Fin 37 → Nat := ![2, 8, 6, 4, 6, 22, 6, 10, 4, 2, 2, 14, 8, 8, 4, 10, 4, 6, 2, 3, 3, 8, 3, 3, 12, 2, 22, 16, 6, 16, 48, 16, 66, 36, 40, 64, 86]

theorem plane484GenLeaf0118 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0118Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0118Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0118Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0118Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 209
  · exact hroot.hOcc 423
  · exact hroot.hOcc 428
  · exact hroot.hOcc 805
  · exact hroot.hOcc 1079
  · exact hroot.hOcc 1084
  · exact hroot.hOcc 1087
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1248
  · exact hroot.hOcc 1289
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1336
  · exact hroot.hOcc 1437
  · exact hroot.hOcc 1503
  · exact hroot.hOcc 1508
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1654
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24

end QiushiMatmul
