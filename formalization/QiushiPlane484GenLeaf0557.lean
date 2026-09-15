import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0557Refs : Fin 42 → RowRef 1665 43 := ![.occ 124, .occ 127, .occ 128, .occ 137, .occ 138, .occ 142, .occ 243, .occ 603, .occ 1071, .occ 1170, .occ 1188, .occ 1200, .occ 1214, .occ 1235, .occ 1238, .occ 1275, .occ 1297, .occ 1303, .occ 1334, .occ 1344, .occ 1345, .occ 1513, .occ 1520, .occ 1534, .occ 1535, .occ 1539, .occ 1547, .occ 1563, .occ 1564, .occ 1580, .occ 1642, .sumGe, .nonneg 2, .nonneg 19, .nonneg 22, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchGe 26 (1), .branchLe 17 (0), .branchLe 42 (0), .branchGe 12 (1)]

def plane484GenLeaf0557Mult : Fin 42 → Nat := ![438, 170, 1176, 92, 1634, 1935, 1421, 800, 98, 200, 14, 142, 257, 617, 136, 729, 149, 465, 1037, 31, 44, 101, 101, 37, 7, 71, 253, 386, 108, 532, 301, 2135, 486, 44, 4110, 5720, 2551, 92, 7645, 1654, 2135, 4511]

theorem plane484GenLeaf0557 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0557Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0557Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0557Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0557Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 142
  · exact hroot.hOcc 243
  · exact hroot.hOcc 603
  · exact hroot.hOcc 1071
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1235
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1275
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1344
  · exact hroot.hOcc 1345
  · exact hroot.hOcc 1513
  · exact hroot.hOcc 1520
  · exact hroot.hOcc 1534
  · exact hroot.hOcc 1535
  · exact hroot.hOcc 1539
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1563
  · exact hroot.hOcc 1564
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1642
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
