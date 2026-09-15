import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0495Refs : Fin 27 → RowRef 1665 43 := ![.occ 124, .occ 131, .occ 138, .occ 140, .occ 142, .occ 143, .occ 442, .occ 501, .occ 513, .occ 596, .occ 769, .occ 844, .occ 858, .occ 1037, .occ 1052, .occ 1356, .occ 1401, .occ 1590, .sumGe, .nonneg 2, .branchGe 15 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 32 (0), .branchLe 36 (0), .branchGe 10 (1), .branchLe 28 (0)]

def plane484GenLeaf0495Mult : Fin 27 → Nat := ![10, 7, 3, 2, 1, 8, 6, 4, 4, 4, 2, 2, 1, 4, 2, 2, 2, 8, 10, 12, 34, 10, 26, 10, 10, 20, 10]

theorem plane484GenLeaf0495 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0495Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0495Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0495Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0495Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 131
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 143
  · exact hroot.hOcc 442
  · exact hroot.hOcc 501
  · exact hroot.hOcc 513
  · exact hroot.hOcc 596
  · exact hroot.hOcc 769
  · exact hroot.hOcc 844
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1037
  · exact hroot.hOcc 1052
  · exact hroot.hOcc 1356
  · exact hroot.hOcc 1401
  · exact hroot.hOcc 1590
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
