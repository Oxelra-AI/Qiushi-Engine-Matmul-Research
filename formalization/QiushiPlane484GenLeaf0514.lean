import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0514Refs : Fin 41 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 124, .occ 125, .occ 126, .occ 127, .occ 128, .occ 130, .occ 131, .occ 138, .occ 140, .occ 251, .occ 294, .occ 323, .occ 378, .occ 647, .occ 671, .occ 1090, .occ 1152, .occ 1158, .occ 1160, .occ 1279, .occ 1303, .occ 1320, .occ 1358, .occ 1472, .occ 1484, .occ 1556, .occ 1615, .occ 1633, .occ 1664, .sumGe, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchLe 34 (0), .branchLe 8 (0), .branchGe 33 (1), .branchGe 3 (1)]

def plane484GenLeaf0514Mult : Fin 41 → Nat := ![98, 43, 23, 22, 196, 57, 1, 38, 34, 112, 56, 172, 112, 420, 32, 258, 2, 124, 46, 68, 10, 56, 56, 228, 168, 228, 56, 138, 90, 34, 78, 486, 728, 1364, 486, 228, 408, 398, 286, 1576, 1348]

theorem plane484GenLeaf0514 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0514Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0514Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0514Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0514Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 251
  · exact hroot.hOcc 294
  · exact hroot.hOcc 323
  · exact hroot.hOcc 378
  · exact hroot.hOcc 647
  · exact hroot.hOcc 671
  · exact hroot.hOcc 1090
  · exact hroot.hOcc 1152
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1279
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1320
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1556
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1633
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
