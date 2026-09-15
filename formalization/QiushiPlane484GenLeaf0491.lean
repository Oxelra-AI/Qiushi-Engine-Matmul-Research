import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0491Refs : Fin 41 → RowRef 1665 43 := ![.occ 92, .occ 130, .occ 131, .occ 133, .occ 138, .occ 170, .occ 186, .occ 522, .occ 595, .occ 607, .occ 619, .occ 897, .occ 904, .occ 1100, .occ 1158, .occ 1168, .occ 1188, .occ 1205, .occ 1206, .occ 1353, .occ 1358, .occ 1602, .occ 1615, .occ 1619, .occ 1629, .occ 1637, .occ 1652, .occ 1660, .sumGe, .nonneg 4, .nonneg 16, .nonneg 20, .nonneg 23, .nonneg 31, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchGe 19 (1), .branchGe 28 (1), .branchLe 12 (0)]

def plane484GenLeaf0491Mult : Fin 41 → Nat := ![16, 19, 73, 40, 67, 9, 3, 30, 15, 12, 3, 6, 3, 1, 43, 3, 3, 2, 1, 3, 34, 33, 16, 3, 12, 15, 30, 9, 85, 33, 93, 33, 164, 1, 290, 39, 84, 152, 236, 117, 60]

theorem plane484GenLeaf0491 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0491Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0491Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0491Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0491Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 92
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 170
  · exact hroot.hOcc 186
  · exact hroot.hOcc 522
  · exact hroot.hOcc 595
  · exact hroot.hOcc 607
  · exact hroot.hOcc 619
  · exact hroot.hOcc 897
  · exact hroot.hOcc 904
  · exact hroot.hOcc 1100
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1637
  · exact hroot.hOcc 1652
  · exact hroot.hOcc 1660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 31
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12

end QiushiMatmul
