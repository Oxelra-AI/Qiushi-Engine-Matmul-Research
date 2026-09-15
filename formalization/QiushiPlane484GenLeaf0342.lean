import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0342Refs : Fin 40 → RowRef 1665 43 := ![.occ 125, .occ 126, .occ 129, .occ 130, .occ 135, .occ 136, .occ 137, .occ 138, .occ 139, .occ 140, .occ 141, .occ 142, .occ 254, .occ 467, .occ 632, .occ 747, .occ 818, .occ 1173, .occ 1179, .occ 1212, .occ 1262, .occ 1406, .occ 1416, .occ 1436, .occ 1484, .occ 1526, .occ 1580, .occ 1656, .sumGe, .nonneg 11, .nonneg 17, .nonneg 21, .branchLe 15 (0), .branchGe 2 (1), .branchLe 23 (0), .branchGe 26 (1), .branchGe 14 (1), .branchLe 36 (0), .branchLe 28 (0), .branchLe 27 (0)]

def plane484GenLeaf0342Mult : Fin 40 → Nat := ![231, 197, 7, 47, 26, 54, 61, 21, 54, 2, 87, 25, 4, 58, 44, 92, 26, 140, 108, 2, 6, 102, 28, 28, 56, 28, 106, 34, 306, 122, 28, 34, 176, 340, 116, 362, 926, 200, 306, 306]

theorem plane484GenLeaf0342 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0342Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0342Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0342Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0342Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 142
  · exact hroot.hOcc 254
  · exact hroot.hOcc 467
  · exact hroot.hOcc 632
  · exact hroot.hOcc 747
  · exact hroot.hOcc 818
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1212
  · exact hroot.hOcc 1262
  · exact hroot.hOcc 1406
  · exact hroot.hOcc 1416
  · exact hroot.hOcc 1436
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1526
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27

end QiushiMatmul
