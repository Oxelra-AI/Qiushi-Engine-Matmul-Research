import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0145Refs : Fin 41 → RowRef 1665 43 := ![.occ 121, .occ 195, .occ 283, .occ 312, .occ 319, .occ 324, .occ 501, .occ 553, .occ 680, .occ 705, .occ 1101, .occ 1136, .occ 1140, .occ 1151, .occ 1172, .occ 1216, .occ 1269, .occ 1270, .occ 1286, .occ 1353, .occ 1428, .occ 1436, .occ 1459, .occ 1477, .occ 1507, .occ 1523, .occ 1551, .occ 1601, .occ 1625, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 39 (1), .branchLe 16 (0), .branchGe 27 (1), .branchLe 24 (0), .branchLe 12 (0), .branchGe 34 (1)]

def plane484GenLeaf0145Mult : Fin 41 → Nat := ![1, 5, 1, 3, 5, 4, 17, 5, 3, 5, 5, 5, 2, 9, 2, 7, 4, 3, 2, 5, 3, 9, 5, 5, 9, 4, 6, 6, 3, 28, 28, 28, 50, 28, 13, 81, 28, 29, 28, 16, 65]

theorem plane484GenLeaf0145 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hUB_12 : x 12 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0145Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0145Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0145Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0145Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 195
  · exact hroot.hOcc 283
  · exact hroot.hOcc 312
  · exact hroot.hOcc 319
  · exact hroot.hOcc 324
  · exact hroot.hOcc 501
  · exact hroot.hOcc 553
  · exact hroot.hOcc 680
  · exact hroot.hOcc 705
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1286
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1436
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1507
  · exact hroot.hOcc 1523
  · exact hroot.hOcc 1551
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1625
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24
  · change (∑ k, (if k = (12 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_12
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34

end QiushiMatmul
