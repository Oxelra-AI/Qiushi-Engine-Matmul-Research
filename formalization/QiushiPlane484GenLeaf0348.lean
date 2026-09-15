import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0348Refs : Fin 30 → RowRef 1665 43 := ![.occ 123, .occ 126, .occ 127, .occ 129, .occ 137, .occ 141, .occ 142, .occ 205, .occ 247, .occ 325, .occ 385, .occ 477, .occ 703, .occ 1011, .occ 1013, .occ 1146, .occ 1147, .occ 1410, .occ 1491, .occ 1496, .sumGe, .nonneg 3, .nonneg 7, .nonneg 23, .branchGe 2 (1), .branchGe 26 (1), .branchGe 14 (1), .branchGe 36 (1), .branchLe 30 (0), .branchGe 6 (1)]

def plane484GenLeaf0348Mult : Fin 30 → Nat := ![3, 7, 4, 4, 2, 1, 2, 1, 6, 3, 3, 3, 1, 1, 4, 6, 1, 1, 3, 3, 7, 13, 14, 8, 21, 29, 14, 5, 4, 35]

theorem plane484GenLeaf0348 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0348Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0348Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0348Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0348Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 205
  · exact hroot.hOcc 247
  · exact hroot.hOcc 325
  · exact hroot.hOcc 385
  · exact hroot.hOcc 477
  · exact hroot.hOcc 703
  · exact hroot.hOcc 1011
  · exact hroot.hOcc 1013
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1410
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1496
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
