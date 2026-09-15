import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0563Refs : Fin 40 → RowRef 1665 43 := ![.occ 119, .occ 120, .occ 133, .occ 135, .occ 175, .occ 215, .occ 292, .occ 366, .occ 708, .occ 1158, .occ 1168, .occ 1188, .occ 1213, .occ 1225, .occ 1245, .occ 1249, .occ 1253, .occ 1275, .occ 1280, .occ 1293, .occ 1350, .occ 1367, .occ 1439, .occ 1447, .occ 1454, .occ 1483, .occ 1514, .occ 1527, .occ 1607, .occ 1615, .sumGe, .nonneg 16, .nonneg 21, .nonneg 26, .branchGe 15 (1), .branchGe 35 (1), .branchGe 25 (1), .branchLe 29 (0), .branchLe 3 (0), .branchGe 0 (1)]

def plane484GenLeaf0563Mult : Fin 40 → Nat := ![543, 309, 2398, 3242, 511, 216, 132, 3920, 1451, 670, 996, 300, 1522, 104, 498, 382, 132, 600, 844, 516, 508, 892, 746, 52, 26, 378, 46, 90, 1312, 514, 3920, 1184, 8876, 2308, 11548, 3360, 14444, 3920, 2248, 6306]

theorem plane484GenLeaf0563 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0563Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0563Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0563Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0563Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 175
  · exact hroot.hOcc 215
  · exact hroot.hOcc 292
  · exact hroot.hOcc 366
  · exact hroot.hOcc 708
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1225
  · exact hroot.hOcc 1245
  · exact hroot.hOcc 1249
  · exact hroot.hOcc 1253
  · exact hroot.hOcc 1275
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1293
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1439
  · exact hroot.hOcc 1447
  · exact hroot.hOcc 1454
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1514
  · exact hroot.hOcc 1527
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1615
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
