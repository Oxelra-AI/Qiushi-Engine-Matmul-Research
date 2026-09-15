import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0464Refs : Fin 35 → RowRef 1665 43 := ![.occ 122, .occ 124, .occ 125, .occ 127, .occ 133, .occ 138, .occ 140, .occ 171, .occ 191, .occ 267, .occ 419, .occ 693, .occ 808, .occ 814, .occ 872, .occ 1025, .occ 1074, .occ 1082, .occ 1105, .occ 1136, .occ 1159, .occ 1235, .occ 1295, .occ 1297, .occ 1358, .occ 1440, .occ 1615, .sumGe, .nonneg 0, .branchGe 15 (1), .branchLe 35 (0), .branchGe 29 (1), .branchGe 27 (1), .branchGe 4 (1), .branchGe 5 (1)]

def plane484GenLeaf0464Mult : Fin 35 → Nat := ![2, 2, 11, 1, 6, 1, 4, 10, 8, 6, 12, 3, 6, 1, 1, 1, 7, 8, 1, 4, 2, 3, 7, 1, 4, 1, 6, 14, 2, 63, 11, 53, 9, 53, 32]

theorem plane484GenLeaf0464 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0464Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0464Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0464Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0464Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 171
  · exact hroot.hOcc 191
  · exact hroot.hOcc 267
  · exact hroot.hOcc 419
  · exact hroot.hOcc 693
  · exact hroot.hOcc 808
  · exact hroot.hOcc 814
  · exact hroot.hOcc 872
  · exact hroot.hOcc 1025
  · exact hroot.hOcc 1074
  · exact hroot.hOcc 1082
  · exact hroot.hOcc 1105
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1235
  · exact hroot.hOcc 1295
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1615
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
