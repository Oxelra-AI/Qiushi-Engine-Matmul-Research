import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0253Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 122, .occ 123, .occ 125, .occ 129, .occ 130, .occ 134, .occ 135, .occ 136, .occ 137, .occ 139, .occ 183, .occ 215, .occ 289, .occ 570, .occ 618, .occ 740, .occ 741, .occ 1158, .occ 1170, .occ 1173, .occ 1190, .occ 1191, .occ 1196, .occ 1226, .occ 1257, .occ 1470, .occ 1481, .occ 1483, .occ 1559, .occ 1567, .occ 1601, .occ 1615, .sumGe, .nonneg 12, .nonneg 17, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchGe 16 (1), .branchGe 13 (1)]

def plane484GenLeaf0253Mult : Fin 44 → Nat := ![91, 109, 94, 6, 55, 59, 27, 68, 161, 97, 37, 178, 2, 94, 78, 56, 38, 24, 16, 26, 70, 148, 30, 2, 16, 12, 10, 22, 132, 8, 20, 42, 6, 274, 250, 204, 52, 600, 20, 138, 140, 190, 648, 1006]

theorem plane484GenLeaf0253 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0253Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0253Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0253Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0253Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 183
  · exact hroot.hOcc 215
  · exact hroot.hOcc 289
  · exact hroot.hOcc 570
  · exact hroot.hOcc 618
  · exact hroot.hOcc 740
  · exact hroot.hOcc 741
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1226
  · exact hroot.hOcc 1257
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1559
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1615
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
