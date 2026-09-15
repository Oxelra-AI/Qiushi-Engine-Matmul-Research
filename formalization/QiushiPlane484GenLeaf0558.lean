import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0558Refs : Fin 43 → RowRef 1665 43 := ![.occ 123, .occ 138, .occ 140, .occ 142, .occ 217, .occ 243, .occ 256, .occ 709, .occ 718, .occ 735, .occ 747, .occ 779, .occ 787, .occ 803, .occ 1043, .occ 1052, .occ 1214, .occ 1303, .occ 1334, .occ 1340, .occ 1377, .occ 1392, .occ 1398, .occ 1417, .occ 1418, .occ 1432, .occ 1439, .occ 1440, .occ 1462, .occ 1472, .occ 1483, .occ 1496, .occ 1607, .sumGe, .nonneg 18, .nonneg 22, .nonneg 25, .branchGe 15 (1), .branchGe 35 (1), .branchGe 26 (1), .branchLe 17 (0), .branchGe 42 (1), .branchLe 16 (0)]

def plane484GenLeaf0558Mult : Fin 43 → Nat := ![14, 345, 1071, 409, 223, 911, 46, 105, 12, 267, 564, 29, 103, 413, 35, 633, 137, 37, 160, 23, 380, 909, 183, 136, 12, 9, 273, 177, 46, 12, 91, 816, 857, 1266, 79, 1990, 432, 2792, 4698, 6723, 12, 4796, 857]

theorem plane484GenLeaf0558 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0558Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0558Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0558Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0558Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 217
  · exact hroot.hOcc 243
  · exact hroot.hOcc 256
  · exact hroot.hOcc 709
  · exact hroot.hOcc 718
  · exact hroot.hOcc 735
  · exact hroot.hOcc 747
  · exact hroot.hOcc 779
  · exact hroot.hOcc 787
  · exact hroot.hOcc 803
  · exact hroot.hOcc 1043
  · exact hroot.hOcc 1052
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1377
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1417
  · exact hroot.hOcc 1418
  · exact hroot.hOcc 1432
  · exact hroot.hOcc 1439
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1607
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16

end QiushiMatmul
