import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0474Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 130, .occ 131, .occ 135, .occ 140, .occ 163, .occ 170, .occ 579, .occ 707, .occ 971, .occ 1158, .occ 1188, .occ 1205, .occ 1241, .occ 1250, .occ 1275, .occ 1339, .occ 1353, .occ 1385, .occ 1394, .occ 1402, .occ 1453, .occ 1454, .occ 1489, .occ 1535, .occ 1536, .occ 1560, .occ 1580, .occ 1601, .occ 1615, .occ 1641, .sumGe, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 24, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 0 (1), .branchLe 25 (0), .branchLe 3 (0), .branchLe 38 (0), .branchGe 20 (1)]

def plane484GenLeaf0474Mult : Fin 44 → Nat := ![13105, 16678, 49743, 35713, 40244, 6007, 11322, 9796, 2674, 5901, 13927, 7142, 7245, 8919, 1236, 9022, 3084, 4928, 2214, 6424, 7265, 780, 7604, 2674, 2555, 4743, 1840, 2254, 12470, 10312, 4214, 49743, 24239, 420, 15144, 137227, 197713, 19652, 38231, 74094, 4928, 20913, 46659, 162587]

theorem plane484GenLeaf0474 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0474Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0474Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0474Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0474Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 135
  · exact hroot.hOcc 140
  · exact hroot.hOcc 163
  · exact hroot.hOcc 170
  · exact hroot.hOcc 579
  · exact hroot.hOcc 707
  · exact hroot.hOcc 971
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1241
  · exact hroot.hOcc 1250
  · exact hroot.hOcc 1275
  · exact hroot.hOcc 1339
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1394
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1453
  · exact hroot.hOcc 1454
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1535
  · exact hroot.hOcc 1536
  · exact hroot.hOcc 1560
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1641
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20

end QiushiMatmul
