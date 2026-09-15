import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0095Refs : Fin 42 → RowRef 1665 43 := ![.occ 122, .occ 124, .occ 125, .occ 127, .occ 128, .occ 130, .occ 141, .occ 346, .occ 385, .occ 428, .occ 792, .occ 1041, .occ 1056, .occ 1077, .occ 1145, .occ 1151, .occ 1243, .occ 1244, .occ 1392, .occ 1408, .occ 1416, .occ 1423, .occ 1442, .occ 1444, .occ 1445, .occ 1573, .occ 1600, .occ 1617, .occ 1639, .occ 1658, .occ 1663, .sumGe, .nonneg 18, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchGe 26 (1), .branchLe 37 (0), .branchLe 28 (0), .branchGe 38 (1)]

def plane484GenLeaf0095Mult : Fin 42 → Nat := ![293, 77, 57, 171, 48, 750, 148, 360, 392, 398, 112, 68, 112, 756, 432, 344, 42, 344, 64, 64, 48, 48, 80, 422, 160, 296, 44, 280, 158, 48, 74, 1296, 280, 968, 276, 792, 3950, 952, 1638, 658, 1296, 2902]

theorem plane484GenLeaf0095 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0095Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0095Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0095Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0095Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 141
  · exact hroot.hOcc 346
  · exact hroot.hOcc 385
  · exact hroot.hOcc 428
  · exact hroot.hOcc 792
  · exact hroot.hOcc 1041
  · exact hroot.hOcc 1056
  · exact hroot.hOcc 1077
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1243
  · exact hroot.hOcc 1244
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1408
  · exact hroot.hOcc 1416
  · exact hroot.hOcc 1423
  · exact hroot.hOcc 1442
  · exact hroot.hOcc 1444
  · exact hroot.hOcc 1445
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1600
  · exact hroot.hOcc 1617
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1658
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38

end QiushiMatmul
