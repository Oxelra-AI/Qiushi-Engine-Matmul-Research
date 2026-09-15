import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0562Refs : Fin 36 → RowRef 1665 43 := ![.occ 129, .occ 133, .occ 213, .occ 367, .occ 835, .occ 858, .occ 886, .occ 990, .occ 1121, .occ 1213, .occ 1249, .occ 1278, .occ 1280, .occ 1340, .occ 1367, .occ 1387, .occ 1401, .occ 1439, .occ 1506, .occ 1514, .occ 1527, .occ 1533, .occ 1564, .occ 1638, .occ 1644, .occ 1645, .occ 1657, .sumGe, .nonneg 21, .branchGe 15 (1), .branchGe 35 (1), .branchGe 25 (1), .branchLe 29 (0), .branchLe 3 (0), .branchLe 26 (0), .branchLe 0 (0)]

def plane484GenLeaf0562Mult : Fin 36 → Nat := ![2, 50, 60, 2, 12, 84, 8, 21, 1, 36, 14, 25, 23, 12, 12, 14, 10, 53, 25, 11, 13, 13, 10, 11, 2, 2, 14, 100, 182, 184, 254, 436, 100, 72, 100, 98]

theorem plane484GenLeaf0562 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0562Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0562Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0562Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0562Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 213
  · exact hroot.hOcc 367
  · exact hroot.hOcc 835
  · exact hroot.hOcc 858
  · exact hroot.hOcc 886
  · exact hroot.hOcc 990
  · exact hroot.hOcc 1121
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1249
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1367
  · exact hroot.hOcc 1387
  · exact hroot.hOcc 1401
  · exact hroot.hOcc 1439
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1514
  · exact hroot.hOcc 1527
  · exact hroot.hOcc 1533
  · exact hroot.hOcc 1564
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1645
  · exact hroot.hOcc 1657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
