import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0282Refs : Fin 44 → RowRef 1665 43 := ![.occ 84, .occ 125, .occ 128, .occ 130, .occ 135, .occ 141, .occ 218, .occ 368, .occ 465, .occ 540, .occ 571, .occ 572, .occ 1150, .occ 1151, .occ 1170, .occ 1190, .occ 1210, .occ 1234, .occ 1313, .occ 1358, .occ 1462, .occ 1481, .occ 1492, .occ 1567, .occ 1603, .occ 1609, .occ 1615, .occ 1620, .occ 1645, .sumGe, .nonneg 4, .nonneg 11, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchLe 13 (0), .branchGe 37 (1), .branchGe 32 (1), .branchLe 10 (0), .branchGe 14 (1)]

def plane484GenLeaf0282Mult : Fin 44 → Nat := ![484, 2149, 394, 329, 476, 345, 1074, 2556, 695, 156, 140, 629, 891, 523, 583, 392, 237, 203, 125, 82, 724, 261, 903, 1355, 213, 226, 442, 65, 226, 2769, 1712, 1792, 1543, 2993, 2769, 2769, 1398, 4982, 2769, 1757, 3989, 5980, 1653, 5767]

theorem plane484GenLeaf0282 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0282Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0282Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0282Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0282Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 135
  · exact hroot.hOcc 141
  · exact hroot.hOcc 218
  · exact hroot.hOcc 368
  · exact hroot.hOcc 465
  · exact hroot.hOcc 540
  · exact hroot.hOcc 571
  · exact hroot.hOcc 572
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1210
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1313
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1645
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (32 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
