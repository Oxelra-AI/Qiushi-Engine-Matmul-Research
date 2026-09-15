import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0317Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 124, .occ 132, .occ 175, .occ 256, .occ 304, .occ 386, .occ 458, .occ 536, .occ 604, .occ 707, .occ 739, .occ 740, .occ 742, .occ 970, .occ 1147, .occ 1200, .occ 1214, .occ 1215, .occ 1216, .occ 1300, .occ 1357, .occ 1436, .occ 1459, .occ 1496, .occ 1573, .occ 1601, .occ 1608, .occ 1650, .sumGe, .nonneg 4, .nonneg 23, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 26 (1), .branchLe 14 (0), .branchLe 1 (0), .branchLe 22 (0), .branchLe 16 (0), .branchGe 0 (1), .branchGe 31 (1), .branchLe 19 (0), .branchGe 13 (1)]

def plane484GenLeaf0317Mult : Fin 44 → Nat := ![393, 190, 56, 51, 410, 119, 97, 283, 247, 130, 325, 22, 1, 22, 49, 139, 55, 66, 109, 64, 47, 75, 105, 55, 183, 161, 56, 139, 51, 583, 205, 183, 528, 635, 205, 1632, 421, 302, 527, 435, 183, 1031, 151, 1457]

theorem plane484GenLeaf0317 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0317Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0317Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0317Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0317Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 124
  · exact hroot.hOcc 132
  · exact hroot.hOcc 175
  · exact hroot.hOcc 256
  · exact hroot.hOcc 304
  · exact hroot.hOcc 386
  · exact hroot.hOcc 458
  · exact hroot.hOcc 536
  · exact hroot.hOcc 604
  · exact hroot.hOcc 707
  · exact hroot.hOcc 739
  · exact hroot.hOcc 740
  · exact hroot.hOcc 742
  · exact hroot.hOcc 970
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1300
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1436
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
