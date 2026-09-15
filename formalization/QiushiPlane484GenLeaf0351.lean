import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0351Refs : Fin 41 → RowRef 1665 43 := ![.occ 123, .occ 124, .occ 127, .occ 128, .occ 138, .occ 141, .occ 142, .occ 386, .occ 672, .occ 757, .occ 816, .occ 818, .occ 827, .occ 1102, .occ 1168, .occ 1179, .occ 1183, .occ 1188, .occ 1190, .occ 1201, .occ 1213, .occ 1220, .occ 1230, .occ 1353, .occ 1387, .occ 1491, .occ 1504, .occ 1547, .occ 1580, .occ 1603, .occ 1632, .occ 1638, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 23 (0), .branchGe 26 (1), .branchGe 14 (1), .branchGe 36 (1), .branchGe 30 (1), .branchGe 12 (1)]

def plane484GenLeaf0351Mult : Fin 41 → Nat := ![25, 25, 7, 21, 12, 16, 4, 14, 28, 18, 38, 32, 44, 2, 4, 4, 4, 14, 12, 2, 10, 8, 6, 20, 10, 8, 10, 14, 10, 10, 10, 6, 62, 32, 62, 14, 166, 100, 118, 184, 186]

theorem plane484GenLeaf0351 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_12 : (1 : Int) ≤ x 12)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0351Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0351Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0351Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0351Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 138
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 386
  · exact hroot.hOcc 672
  · exact hroot.hOcc 757
  · exact hroot.hOcc 816
  · exact hroot.hOcc 818
  · exact hroot.hOcc 827
  · exact hroot.hOcc 1102
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1201
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1230
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1387
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1504
  · exact hroot.hOcc 1547
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1632
  · exact hroot.hOcc 1638
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_12

end QiushiMatmul
