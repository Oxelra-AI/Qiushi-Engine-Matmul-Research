import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0039Refs : Fin 42 → RowRef 1665 43 := ![.occ 120, .occ 128, .occ 133, .occ 134, .occ 143, .occ 211, .occ 511, .occ 704, .occ 707, .occ 779, .occ 835, .occ 981, .occ 1133, .occ 1147, .occ 1168, .occ 1280, .occ 1282, .occ 1329, .occ 1378, .occ 1392, .occ 1397, .occ 1398, .occ 1401, .occ 1500, .occ 1527, .occ 1597, .occ 1606, .occ 1607, .occ 1608, .occ 1647, .sumGe, .nonneg 11, .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchGe 25 (1), .branchLe 33 (0), .branchGe 10 (1), .branchGe 6 (1)]

def plane484GenLeaf0039Mult : Fin 42 → Nat := ![152, 48, 42, 146, 96, 138, 10, 96, 16, 24, 138, 3, 4, 13, 33, 89, 31, 53, 10, 60, 40, 35, 32, 35, 30, 20, 15, 11, 33, 83, 260, 386, 68, 260, 260, 250, 40, 488, 576, 234, 492, 696]

theorem plane484GenLeaf0039 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0039Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0039Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0039Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0039Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 128
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 143
  · exact hroot.hOcc 211
  · exact hroot.hOcc 511
  · exact hroot.hOcc 704
  · exact hroot.hOcc 707
  · exact hroot.hOcc 779
  · exact hroot.hOcc 835
  · exact hroot.hOcc 981
  · exact hroot.hOcc 1133
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1329
  · exact hroot.hOcc 1378
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1397
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1401
  · exact hroot.hOcc 1500
  · exact hroot.hOcc 1527
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1647
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
