import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0388Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 125, .occ 126, .occ 127, .occ 128, .occ 129, .occ 130, .occ 137, .occ 138, .occ 326, .occ 600, .occ 615, .occ 641, .occ 712, .occ 1034, .occ 1173, .occ 1179, .occ 1213, .occ 1230, .occ 1264, .occ 1357, .occ 1383, .occ 1388, .occ 1458, .occ 1459, .occ 1463, .occ 1472, .occ 1478, .occ 1481, .occ 1492, .occ 1624, .sumGe, .nonneg 22, .nonneg 25, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchGe 23 (1), .branchGe 35 (1), .branchGe 30 (1), .branchGe 42 (1), .branchLe 39 (0), .branchGe 1 (1), .branchGe 14 (1)]

def plane484GenLeaf0388Mult : Fin 44 → Nat := ![90, 523, 15, 84, 140, 175, 363, 876, 522, 90, 336, 184, 178, 696, 222, 158, 327, 296, 184, 257, 428, 33, 90, 136, 386, 551, 90, 338, 248, 606, 90, 1398, 406, 904, 876, 1392, 1034, 3608, 2316, 1666, 1998, 876, 1040, 2694]

theorem plane484GenLeaf0388 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_14 : (1 : Int) ≤ x 14)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0388Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0388Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0388Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0388Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 137
  · exact hroot.hOcc 138
  · exact hroot.hOcc 326
  · exact hroot.hOcc 600
  · exact hroot.hOcc 615
  · exact hroot.hOcc 641
  · exact hroot.hOcc 712
  · exact hroot.hOcc 1034
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1230
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1383
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1463
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1624
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (14 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_14

end QiushiMatmul
