import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0423Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 124, .occ 135, .occ 137, .occ 139, .occ 142, .occ 154, .occ 181, .occ 187, .occ 190, .occ 233, .occ 329, .occ 440, .occ 474, .occ 562, .occ 680, .occ 707, .occ 1143, .occ 1161, .occ 1164, .occ 1173, .occ 1183, .occ 1208, .occ 1296, .occ 1312, .occ 1353, .occ 1488, .occ 1529, .occ 1571, .occ 1658, .sumGe, .nonneg 16, .branchLe 15 (0), .branchGe 2 (1), .branchGe 7 (1), .branchLe 6 (0), .branchGe 31 (1), .branchGe 29 (1), .branchLe 36 (0), .branchGe 34 (1), .branchLe 42 (0), .branchGe 21 (1)]

def plane484GenLeaf0423Mult : Fin 43 → Nat := ![38, 22, 28, 25, 45, 11, 18, 38, 62, 18, 22, 6, 15, 54, 12, 56, 34, 2, 10, 2, 2, 10, 2, 22, 6, 10, 10, 8, 10, 42, 12, 82, 14, 12, 78, 278, 82, 104, 156, 70, 174, 74, 246]

theorem plane484GenLeaf0423 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0423Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0423Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0423Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0423Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 142
  · exact hroot.hOcc 154
  · exact hroot.hOcc 181
  · exact hroot.hOcc 187
  · exact hroot.hOcc 190
  · exact hroot.hOcc 233
  · exact hroot.hOcc 329
  · exact hroot.hOcc 440
  · exact hroot.hOcc 474
  · exact hroot.hOcc 562
  · exact hroot.hOcc 680
  · exact hroot.hOcc 707
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1161
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1296
  · exact hroot.hOcc 1312
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21

end QiushiMatmul
