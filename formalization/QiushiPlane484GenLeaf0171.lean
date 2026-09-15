import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0171Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 122, .occ 126, .occ 127, .occ 129, .occ 134, .occ 135, .occ 141, .occ 142, .occ 246, .occ 271, .occ 363, .occ 430, .occ 615, .occ 680, .occ 1196, .occ 1228, .occ 1272, .occ 1273, .occ 1283, .occ 1317, .occ 1394, .occ 1402, .occ 1405, .occ 1419, .occ 1431, .occ 1443, .occ 1477, .occ 1507, .occ 1509, .occ 1511, .sumGe, .nonneg 14, .nonneg 15, .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchGe 30 (1), .branchGe 20 (1), .branchLe 5 (0), .branchLe 31 (0), .branchGe 6 (1)]

def plane484GenLeaf0171Mult : Fin 44 → Nat := ![77, 49, 74, 105, 136, 117, 50, 25, 50, 185, 68, 62, 31, 17, 40, 77, 23, 27, 110, 17, 70, 80, 88, 33, 27, 3, 40, 34, 37, 63, 84, 305, 364, 36, 104, 475, 305, 558, 36, 234, 577, 169, 305, 947]

theorem plane484GenLeaf0171 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0171Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0171Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0171Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0171Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 122
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 246
  · exact hroot.hOcc 271
  · exact hroot.hOcc 363
  · exact hroot.hOcc 430
  · exact hroot.hOcc 615
  · exact hroot.hOcc 680
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1228
  · exact hroot.hOcc 1272
  · exact hroot.hOcc 1273
  · exact hroot.hOcc 1283
  · exact hroot.hOcc 1317
  · exact hroot.hOcc 1394
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1419
  · exact hroot.hOcc 1431
  · exact hroot.hOcc 1443
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1507
  · exact hroot.hOcc 1509
  · exact hroot.hOcc 1511
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6

end QiushiMatmul
