import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0187Refs : Fin 42 → RowRef 1665 43 := ![.occ 119, .occ 122, .occ 143, .occ 212, .occ 227, .occ 243, .occ 307, .occ 312, .occ 316, .occ 390, .occ 554, .occ 603, .occ 633, .occ 708, .occ 1166, .occ 1216, .occ 1227, .occ 1274, .occ 1293, .occ 1296, .occ 1326, .occ 1353, .occ 1398, .occ 1418, .occ 1488, .occ 1500, .occ 1510, .occ 1551, .occ 1601, .sumGe, .nonneg 0, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchLe 1 (0), .branchLe 5 (0), .branchGe 7 (1), .branchGe 39 (1), .branchGe 34 (1)]

def plane484GenLeaf0187Mult : Fin 42 → Nat := ![40, 2, 32, 119, 40, 38, 29, 72, 14, 130, 80, 36, 191, 11, 130, 10, 28, 2, 118, 35, 14, 2, 65, 65, 12, 16, 53, 30, 53, 195, 51, 12, 151, 328, 679, 195, 147, 193, 184, 550, 496, 947]

theorem plane484GenLeaf0187 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_34 : (1 : Int) ≤ x 34)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0187Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0187Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0187Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0187Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 122
  · exact hroot.hOcc 143
  · exact hroot.hOcc 212
  · exact hroot.hOcc 227
  · exact hroot.hOcc 243
  · exact hroot.hOcc 307
  · exact hroot.hOcc 312
  · exact hroot.hOcc 316
  · exact hroot.hOcc 390
  · exact hroot.hOcc 554
  · exact hroot.hOcc 603
  · exact hroot.hOcc 633
  · exact hroot.hOcc 708
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1227
  · exact hroot.hOcc 1274
  · exact hroot.hOcc 1293
  · exact hroot.hOcc 1296
  · exact hroot.hOcc 1326
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1418
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1500
  · exact hroot.hOcc 1510
  · exact hroot.hOcc 1551
  · exact hroot.hOcc 1601
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (34 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_34

end QiushiMatmul
