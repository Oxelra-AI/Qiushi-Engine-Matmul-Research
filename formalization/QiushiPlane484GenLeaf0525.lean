import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0525Refs : Fin 42 → RowRef 1665 43 := ![.occ 119, .occ 120, .occ 131, .occ 135, .occ 138, .occ 141, .occ 186, .occ 239, .occ 380, .occ 526, .occ 676, .occ 815, .occ 878, .occ 953, .occ 1159, .occ 1188, .occ 1191, .occ 1200, .occ 1206, .occ 1314, .occ 1342, .occ 1429, .occ 1483, .occ 1484, .occ 1506, .occ 1562, .occ 1576, .occ 1630, .occ 1660, .sumGe, .nonneg 2, .nonneg 26, .nonneg 39, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 30 (0), .branchGe 34 (1), .branchLe 9 (0), .branchGe 18 (1), .branchLe 1 (0), .branchGe 12 (1)]

def plane484GenLeaf0525Mult : Fin 42 → Nat := ![29, 94, 35, 190, 145, 33, 59, 93, 19, 104, 82, 2, 311, 156, 111, 60, 33, 119, 26, 74, 48, 33, 34, 191, 78, 9, 5, 44, 43, 345, 432, 33, 17, 1184, 362, 35, 166, 1044, 130, 547, 275, 912]

theorem plane484GenLeaf0525 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0525Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0525Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0525Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0525Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 131
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 141
  · exact hroot.hOcc 186
  · exact hroot.hOcc 239
  · exact hroot.hOcc 380
  · exact hroot.hOcc 526
  · exact hroot.hOcc 676
  · exact hroot.hOcc 815
  · exact hroot.hOcc 878
  · exact hroot.hOcc 953
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1314
  · exact hroot.hOcc 1342
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1576
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 39
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
