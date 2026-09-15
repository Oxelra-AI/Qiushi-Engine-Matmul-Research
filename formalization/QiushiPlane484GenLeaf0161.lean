import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0161Refs : Fin 41 → RowRef 1665 43 := ![.occ 142, .occ 144, .occ 329, .occ 440, .occ 508, .occ 559, .occ 680, .occ 716, .occ 767, .occ 777, .occ 841, .occ 842, .occ 858, .occ 964, .occ 972, .occ 1082, .occ 1097, .occ 1183, .occ 1324, .occ 1330, .occ 1373, .occ 1409, .occ 1431, .occ 1491, .occ 1543, .occ 1550, .occ 1603, .occ 1608, .occ 1628, .occ 1658, .sumGe, .nonneg 1, .nonneg 2, .nonneg 15, .branchGe 29 (1), .branchLe 35 (0), .branchGe 7 (1), .branchLe 18 (0), .branchLe 30 (0), .branchGe 21 (1), .branchGe 25 (1)]

def plane484GenLeaf0161Mult : Fin 41 → Nat := ![59, 20, 58, 59, 12, 20, 18, 2, 7, 20, 6, 14, 59, 23, 36, 5, 31, 4, 8, 34, 2, 19, 5, 2, 2, 33, 2, 2, 2, 3, 63, 20, 2, 310, 126, 63, 164, 2, 31, 416, 356]

theorem plane484GenLeaf0161 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_21 : (1 : Int) ≤ x 21)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0161Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0161Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0161Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0161Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 142
  · exact hroot.hOcc 144
  · exact hroot.hOcc 329
  · exact hroot.hOcc 440
  · exact hroot.hOcc 508
  · exact hroot.hOcc 559
  · exact hroot.hOcc 680
  · exact hroot.hOcc 716
  · exact hroot.hOcc 767
  · exact hroot.hOcc 777
  · exact hroot.hOcc 841
  · exact hroot.hOcc 842
  · exact hroot.hOcc 858
  · exact hroot.hOcc 964
  · exact hroot.hOcc 972
  · exact hroot.hOcc 1082
  · exact hroot.hOcc 1097
  · exact hroot.hOcc 1183
  · exact hroot.hOcc 1324
  · exact hroot.hOcc 1330
  · exact hroot.hOcc 1373
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1431
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1543
  · exact hroot.hOcc 1550
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_21
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25

end QiushiMatmul
