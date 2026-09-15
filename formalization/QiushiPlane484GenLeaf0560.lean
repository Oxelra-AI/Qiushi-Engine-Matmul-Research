import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0560Refs : Fin 38 → RowRef 1665 43 := ![.occ 138, .occ 140, .occ 141, .occ 142, .occ 243, .occ 292, .occ 296, .occ 400, .occ 673, .occ 755, .occ 959, .occ 1013, .occ 1191, .occ 1205, .occ 1254, .occ 1297, .occ 1303, .occ 1334, .occ 1341, .occ 1393, .occ 1398, .occ 1449, .occ 1467, .occ 1544, .occ 1546, .occ 1547, .occ 1555, .occ 1561, .occ 1590, .sumGe, .nonneg 1, .nonneg 20, .nonneg 22, .branchGe 15 (1), .branchGe 35 (1), .branchGe 26 (1), .branchGe 17 (1), .branchLe 5 (0)]

def plane484GenLeaf0560Mult : Fin 38 → Nat := ![29, 33, 4, 29, 3, 9, 12, 3, 12, 5, 15, 13, 4, 2, 10, 4, 2, 5, 5, 1, 14, 2, 11, 9, 2, 6, 3, 13, 1, 33, 14, 80, 82, 120, 100, 165, 119, 28]

theorem plane484GenLeaf0560 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0560Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0560Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0560Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0560Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 243
  · exact hroot.hOcc 292
  · exact hroot.hOcc 296
  · exact hroot.hOcc 400
  · exact hroot.hOcc 673
  · exact hroot.hOcc 755
  · exact hroot.hOcc 959
  · exact hroot.hOcc 1013
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1254
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1341
  · exact hroot.hOcc 1393
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1544
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1555
  · exact hroot.hOcc 1561
  · exact hroot.hOcc 1590
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5

end QiushiMatmul
