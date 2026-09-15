import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0115Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 125, .occ 127, .occ 139, .occ 209, .occ 354, .occ 359, .occ 707, .occ 861, .occ 920, .occ 992, .occ 1145, .occ 1238, .occ 1263, .occ 1264, .occ 1294, .occ 1297, .occ 1384, .occ 1400, .occ 1422, .occ 1438, .occ 1455, .occ 1503, .occ 1504, .occ 1541, .occ 1545, .occ 1573, .occ 1610, .occ 1620, .occ 1624, .occ 1657, .sumGe, .nonneg 0, .nonneg 1, .nonneg 19, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchGe 36 (1), .branchGe 26 (1), .branchLe 21 (0), .branchGe 18 (1)]

def plane484GenLeaf0115Mult : Fin 43 → Nat := ![2902, 1156, 2244, 9721, 2514, 7420, 4018, 6386, 461, 3600, 65, 510, 1688, 676, 2108, 1208, 668, 1756, 3520, 1154, 5118, 1178, 534, 4140, 1617, 1030, 1846, 1020, 2825, 1827, 2847, 13746, 1214, 1527, 22798, 13078, 10234, 13746, 24304, 28718, 27000, 510, 48844]

theorem plane484GenLeaf0115 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0115Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0115Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0115Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0115Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 139
  · exact hroot.hOcc 209
  · exact hroot.hOcc 354
  · exact hroot.hOcc 359
  · exact hroot.hOcc 707
  · exact hroot.hOcc 861
  · exact hroot.hOcc 920
  · exact hroot.hOcc 992
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1238
  · exact hroot.hOcc 1263
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1294
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1400
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1438
  · exact hroot.hOcc 1455
  · exact hroot.hOcc 1503
  · exact hroot.hOcc 1504
  · exact hroot.hOcc 1541
  · exact hroot.hOcc 1545
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
