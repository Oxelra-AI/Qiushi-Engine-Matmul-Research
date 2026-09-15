import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0099Refs : Fin 43 → RowRef 1665 43 := ![.occ 122, .occ 125, .occ 137, .occ 139, .occ 145, .occ 352, .occ 499, .occ 565, .occ 652, .occ 836, .occ 991, .occ 1085, .occ 1168, .occ 1186, .occ 1240, .occ 1247, .occ 1250, .occ 1301, .occ 1382, .occ 1448, .occ 1451, .occ 1522, .occ 1541, .occ 1607, .occ 1617, .occ 1644, .occ 1655, .sumGe, .nonneg 0, .nonneg 1, .nonneg 2, .nonneg 11, .nonneg 12, .nonneg 13, .nonneg 16, .branchLe 15 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchGe 26 (1), .branchLe 37 (0), .branchGe 28 (1), .branchGe 8 (1)]

def plane484GenLeaf0099Mult : Fin 43 → Nat := ![215, 162, 66, 115, 92, 69, 39, 79, 4, 31, 68, 62, 37, 16, 25, 22, 3, 102, 87, 3, 31, 6, 56, 154, 1, 60, 20, 275, 9, 75, 29, 434, 28, 3, 92, 203, 275, 538, 216, 375, 275, 382, 1028]

theorem plane484GenLeaf0099 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0099Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0099Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0099Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0099Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 137
  · exact hroot.hOcc 139
  · exact hroot.hOcc 145
  · exact hroot.hOcc 352
  · exact hroot.hOcc 499
  · exact hroot.hOcc 565
  · exact hroot.hOcc 652
  · exact hroot.hOcc 836
  · exact hroot.hOcc 991
  · exact hroot.hOcc 1085
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1240
  · exact hroot.hOcc 1247
  · exact hroot.hOcc 1250
  · exact hroot.hOcc 1301
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1448
  · exact hroot.hOcc 1451
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1541
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1617
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8

end QiushiMatmul
