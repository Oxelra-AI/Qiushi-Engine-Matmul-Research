import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0391Refs : Fin 42 → RowRef 1665 43 := ![.occ 131, .occ 137, .occ 138, .occ 311, .occ 615, .occ 639, .occ 709, .occ 742, .occ 754, .occ 774, .occ 1140, .occ 1143, .occ 1147, .occ 1150, .occ 1158, .occ 1179, .occ 1205, .occ 1224, .occ 1246, .occ 1357, .occ 1383, .occ 1425, .occ 1459, .occ 1463, .occ 1483, .occ 1484, .occ 1492, .occ 1573, .occ 1602, .occ 1639, .sumGe, .nonneg 15, .nonneg 18, .nonneg 25, .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchGe 30 (1), .branchGe 42 (1), .branchGe 39 (1), .branchGe 37 (1)]

def plane484GenLeaf0391Mult : Fin 42 → Nat := ![22, 29, 38, 22, 5, 77, 37, 36, 46, 58, 17, 30, 24, 18, 33, 1, 18, 23, 43, 18, 11, 11, 6, 45, 24, 12, 30, 4, 27, 10, 105, 42, 8, 18, 96, 105, 356, 141, 248, 238, 215, 435]

theorem plane484GenLeaf0391 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0391Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0391Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0391Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0391Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 131
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 311
  · exact hroot.hOcc 615
  · exact hroot.hOcc 639
  · exact hroot.hOcc 709
  · exact hroot.hOcc 742
  · exact hroot.hOcc 754
  · exact hroot.hOcc 774
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1224
  · exact hroot.hOcc 1246
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1383
  · exact hroot.hOcc 1425
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1463
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1639
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
