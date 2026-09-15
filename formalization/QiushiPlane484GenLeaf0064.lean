import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0064Refs : Fin 39 → RowRef 1665 43 := ![.occ 122, .occ 124, .occ 132, .occ 137, .occ 138, .occ 175, .occ 385, .occ 460, .occ 585, .occ 588, .occ 642, .occ 860, .occ 941, .occ 1168, .occ 1249, .occ 1252, .occ 1253, .occ 1256, .occ 1297, .occ 1299, .occ 1300, .occ 1314, .occ 1322, .occ 1357, .occ 1537, .occ 1540, .occ 1553, .sumGe, .nonneg 0, .nonneg 1, .nonneg 2, .nonneg 3, .nonneg 4, .branchLe 15 (0), .branchLe 29 (0), .branchGe 13 (1), .branchLe 42 (0), .branchGe 10 (1), .branchLe 28 (0)]

def plane484GenLeaf0064Mult : Fin 39 → Nat := ![7554, 7554, 771, 1812, 534, 6567, 628, 314, 2440, 2016, 608, 676, 2188, 602, 242, 2064, 3108, 1147, 3416, 88, 3710, 77, 314, 71, 562, 186, 910, 7554, 457, 1304, 2346, 314, 28644, 3362, 7466, 29272, 7554, 37556, 7554]

theorem plane484GenLeaf0064 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0064Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0064Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0064Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0064Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 175
  · exact hroot.hOcc 385
  · exact hroot.hOcc 460
  · exact hroot.hOcc 585
  · exact hroot.hOcc 588
  · exact hroot.hOcc 642
  · exact hroot.hOcc 860
  · exact hroot.hOcc 941
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1249
  · exact hroot.hOcc 1252
  · exact hroot.hOcc 1253
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1299
  · exact hroot.hOcc 1300
  · exact hroot.hOcc 1314
  · exact hroot.hOcc 1322
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1537
  · exact hroot.hOcc 1540
  · exact hroot.hOcc 1553
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
