import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0501Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 126, .occ 129, .occ 131, .occ 138, .occ 144, .occ 283, .occ 337, .occ 539, .occ 700, .occ 822, .occ 844, .occ 866, .occ 978, .occ 1052, .occ 1091, .occ 1092, .occ 1136, .occ 1190, .occ 1191, .occ 1229, .occ 1310, .occ 1409, .occ 1424, .occ 1507, .occ 1509, .occ 1552, .occ 1590, .occ 1628, .occ 1631, .occ 1664, .sumGe, .nonneg 0, .nonneg 1, .nonneg 6, .nonneg 10, .nonneg 11, .branchGe 15 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 32 (0), .branchGe 14 (1), .branchGe 3 (1)]

def plane484GenLeaf0501Mult : Fin 43 → Nat := ![346, 306, 153, 287, 234, 346, 108, 98, 1, 259, 108, 36, 37, 374, 165, 20, 63, 216, 54, 54, 147, 69, 166, 190, 39, 61, 2, 216, 41, 45, 41, 648, 395, 108, 533, 422, 432, 1619, 648, 1559, 648, 1406, 1769]

theorem plane484GenLeaf0501 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0501Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0501Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0501Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0501Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 126
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 138
  · exact hroot.hOcc 144
  · exact hroot.hOcc 283
  · exact hroot.hOcc 337
  · exact hroot.hOcc 539
  · exact hroot.hOcc 700
  · exact hroot.hOcc 822
  · exact hroot.hOcc 844
  · exact hroot.hOcc 866
  · exact hroot.hOcc 978
  · exact hroot.hOcc 1052
  · exact hroot.hOcc 1091
  · exact hroot.hOcc 1092
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1229
  · exact hroot.hOcc 1310
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1424
  · exact hroot.hOcc 1507
  · exact hroot.hOcc 1509
  · exact hroot.hOcc 1552
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 10
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
