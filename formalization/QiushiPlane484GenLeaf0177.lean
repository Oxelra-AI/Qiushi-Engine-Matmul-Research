import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0177Refs : Fin 39 → RowRef 1665 43 := ![.occ 121, .occ 124, .occ 129, .occ 134, .occ 141, .occ 716, .occ 734, .occ 777, .occ 1025, .occ 1136, .occ 1224, .occ 1325, .occ 1362, .occ 1370, .occ 1372, .occ 1375, .occ 1376, .occ 1379, .occ 1383, .occ 1405, .occ 1406, .occ 1407, .occ 1443, .occ 1471, .occ 1529, .occ 1530, .occ 1625, .occ 1656, .sumGe, .nonneg 0, .nonneg 13, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchGe 18 (1), .branchGe 42 (1), .branchGe 5 (1)]

def plane484GenLeaf0177Mult : Fin 39 → Nat := ![118, 164, 84, 52, 2, 116, 4, 82, 14, 78, 18, 12, 116, 85, 59, 42, 29, 59, 54, 33, 7, 10, 26, 44, 150, 14, 6, 54, 268, 18, 392, 268, 104, 648, 268, 562, 516, 382, 780]

theorem plane484GenLeaf0177 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0177Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0177Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0177Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0177Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 141
  · exact hroot.hOcc 716
  · exact hroot.hOcc 734
  · exact hroot.hOcc 777
  · exact hroot.hOcc 1025
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1224
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1362
  · exact hroot.hOcc 1370
  · exact hroot.hOcc 1372
  · exact hroot.hOcc 1375
  · exact hroot.hOcc 1376
  · exact hroot.hOcc 1379
  · exact hroot.hOcc 1383
  · exact hroot.hOcc 1405
  · exact hroot.hOcc 1406
  · exact hroot.hOcc 1407
  · exact hroot.hOcc 1443
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1529
  · exact hroot.hOcc 1530
  · exact hroot.hOcc 1625
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
