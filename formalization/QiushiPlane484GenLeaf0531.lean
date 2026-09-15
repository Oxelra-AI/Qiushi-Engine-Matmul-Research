import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0531Refs : Fin 43 → RowRef 1665 43 := ![.occ 124, .occ 171, .occ 191, .occ 200, .occ 295, .occ 377, .occ 380, .occ 383, .occ 591, .occ 810, .occ 813, .occ 814, .occ 875, .occ 1205, .occ 1208, .occ 1236, .occ 1239, .occ 1240, .occ 1246, .occ 1260, .occ 1277, .occ 1288, .occ 1292, .occ 1394, .occ 1439, .occ 1505, .occ 1651, .occ 1659, .occ 1660, .sumGe, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchLe 1 (0), .branchLe 0 (0), .branchLe 19 (0), .branchLe 2 (0), .branchLe 14 (0), .branchLe 40 (0), .branchLe 3 (0), .branchGe 4 (1)]

def plane484GenLeaf0531Mult : Fin 43 → Nat := ![2, 27, 18, 18, 12, 2, 5, 29, 41, 12, 10, 2, 4, 4, 5, 1, 10, 25, 7, 8, 1, 23, 8, 3, 28, 5, 21, 1, 3, 59, 101, 118, 30, 37, 186, 29, 55, 55, 57, 59, 59, 59, 123]

theorem plane484GenLeaf0531 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0531Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0531Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0531Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0531Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 171
  · exact hroot.hOcc 191
  · exact hroot.hOcc 200
  · exact hroot.hOcc 295
  · exact hroot.hOcc 377
  · exact hroot.hOcc 380
  · exact hroot.hOcc 383
  · exact hroot.hOcc 591
  · exact hroot.hOcc 810
  · exact hroot.hOcc 813
  · exact hroot.hOcc 814
  · exact hroot.hOcc 875
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1239
  · exact hroot.hOcc 1240
  · exact hroot.hOcc 1246
  · exact hroot.hOcc 1260
  · exact hroot.hOcc 1277
  · exact hroot.hOcc 1288
  · exact hroot.hOcc 1292
  · exact hroot.hOcc 1394
  · exact hroot.hOcc 1439
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1651
  · exact hroot.hOcc 1659
  · exact hroot.hOcc 1660
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4

end QiushiMatmul
