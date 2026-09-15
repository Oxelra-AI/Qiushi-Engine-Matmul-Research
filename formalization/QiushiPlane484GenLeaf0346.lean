import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0346Refs : Fin 44 → RowRef 1665 43 := ![.occ 125, .occ 128, .occ 129, .occ 135, .occ 137, .occ 138, .occ 140, .occ 565, .occ 631, .occ 818, .occ 836, .occ 1173, .occ 1186, .occ 1214, .occ 1229, .occ 1382, .occ 1384, .occ 1481, .occ 1488, .occ 1492, .occ 1513, .occ 1522, .occ 1524, .occ 1525, .occ 1567, .occ 1607, .occ 1622, .occ 1630, .occ 1644, .occ 1656, .sumGe, .nonneg 3, .nonneg 5, .nonneg 9, .nonneg 11, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchGe 26 (1), .branchGe 14 (1), .branchLe 36 (0), .branchGe 28 (1), .branchGe 8 (1)]

def plane484GenLeaf0346Mult : Fin 44 → Nat := ![603, 394, 394, 229, 92, 61, 47, 25, 368, 13, 72, 43, 140, 42, 89, 34, 127, 107, 106, 76, 9, 88, 73, 43, 139, 131, 35, 22, 89, 98, 603, 165, 1308, 335, 288, 111, 1039, 34, 450, 798, 2076, 603, 394, 1871]

theorem plane484GenLeaf0346 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0346Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0346Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0346Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0346Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 135
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 565
  · exact hroot.hOcc 631
  · exact hroot.hOcc 818
  · exact hroot.hOcc 836
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1229
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1513
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1525
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 3
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 9
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
