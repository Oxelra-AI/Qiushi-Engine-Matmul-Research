import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0459Refs : Fin 42 → RowRef 1665 43 := ![.occ 136, .occ 138, .occ 140, .occ 309, .occ 419, .occ 466, .occ 737, .occ 1102, .occ 1140, .occ 1172, .occ 1188, .occ 1225, .occ 1229, .occ 1276, .occ 1309, .occ 1310, .occ 1330, .occ 1344, .occ 1353, .occ 1393, .occ 1402, .occ 1415, .occ 1419, .occ 1484, .occ 1520, .occ 1536, .occ 1563, .occ 1629, .occ 1646, .sumGe, .nonneg 23, .nonneg 26, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchGe 29 (1), .branchGe 27 (1), .branchLe 8 (0), .branchLe 4 (0), .branchLe 16 (0), .branchGe 22 (1)]

def plane484GenLeaf0459Mult : Fin 42 → Nat := ![1245, 6875, 7877, 5691, 327, 3844, 1054, 923, 1245, 1333, 1478, 1478, 746, 2672, 583, 215, 5381, 1181, 930, 2231, 1274, 2168, 435, 1960, 3497, 2872, 327, 4361, 1002, 13483, 923, 12925, 32271, 11523, 8507, 11220, 18367, 8851, 7793, 13483, 11220, 30399]

theorem plane484GenLeaf0459 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0459Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0459Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0459Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0459Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 309
  · exact hroot.hOcc 419
  · exact hroot.hOcc 466
  · exact hroot.hOcc 737
  · exact hroot.hOcc 1102
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1225
  · exact hroot.hOcc 1229
  · exact hroot.hOcc 1276
  · exact hroot.hOcc 1309
  · exact hroot.hOcc 1310
  · exact hroot.hOcc 1330
  · exact hroot.hOcc 1344
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1393
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1415
  · exact hroot.hOcc 1419
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1520
  · exact hroot.hOcc 1536
  · exact hroot.hOcc 1563
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1646
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
