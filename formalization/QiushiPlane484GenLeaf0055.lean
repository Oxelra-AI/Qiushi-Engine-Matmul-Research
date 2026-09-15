import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0055Refs : Fin 41 → RowRef 1665 43 := ![.occ 99, .occ 120, .occ 126, .occ 128, .occ 132, .occ 136, .occ 140, .occ 141, .occ 160, .occ 177, .occ 440, .occ 587, .occ 782, .occ 843, .occ 940, .occ 1186, .occ 1196, .occ 1206, .occ 1309, .occ 1313, .occ 1398, .occ 1428, .occ 1487, .occ 1523, .occ 1562, .occ 1590, .occ 1606, .occ 1607, .occ 1630, .occ 1634, .sumGe, .nonneg 2, .branchLe 15 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchGe 17 (1), .branchGe 7 (1), .branchGe 10 (1), .branchLe 18 (0), .branchLe 36 (0)]

def plane484GenLeaf0055Mult : Fin 41 → Nat := ![71, 189, 40, 116, 22, 219, 16, 90, 6, 357, 56, 1, 36, 215, 139, 42, 14, 111, 28, 26, 61, 14, 37, 22, 8, 84, 70, 14, 58, 95, 385, 62, 116, 301, 385, 385, 1226, 206, 963, 273, 371]

theorem plane484GenLeaf0055 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0055Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0055Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0055Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0055Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 99
  · exact hroot.hOcc 120
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 160
  · exact hroot.hOcc 177
  · exact hroot.hOcc 440
  · exact hroot.hOcc 587
  · exact hroot.hOcc 782
  · exact hroot.hOcc 843
  · exact hroot.hOcc 940
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1309
  · exact hroot.hOcc 1313
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1487
  · exact hroot.hOcc 1523
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1634
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36

end QiushiMatmul
