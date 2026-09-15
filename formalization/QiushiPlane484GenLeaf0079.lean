import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0079Refs : Fin 44 → RowRef 1665 43 := ![.occ 124, .occ 129, .occ 134, .occ 137, .occ 141, .occ 236, .occ 405, .occ 436, .occ 581, .occ 724, .occ 728, .occ 742, .occ 758, .occ 761, .occ 774, .occ 823, .occ 887, .occ 1122, .occ 1154, .occ 1172, .occ 1173, .occ 1220, .occ 1375, .occ 1376, .occ 1397, .occ 1426, .occ 1433, .occ 1439, .occ 1459, .occ 1462, .occ 1537, .occ 1651, .sumGe, .nonneg 0, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchGe 42 (1), .branchLe 9 (0), .branchGe 20 (1), .branchLe 41 (0), .branchGe 37 (1)]

def plane484GenLeaf0079Mult : Fin 44 → Nat := ![4, 68, 36, 24, 58, 151, 8, 16, 22, 42, 115, 37, 19, 46, 7, 15, 20, 22, 22, 12, 12, 26, 45, 12, 13, 36, 55, 15, 42, 1, 6, 28, 151, 25, 86, 101, 129, 98, 296, 334, 151, 446, 114, 554]

theorem plane484GenLeaf0079 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0079Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0079Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0079Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0079Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 124
  · exact hroot.hOcc 129
  · exact hroot.hOcc 134
  · exact hroot.hOcc 137
  · exact hroot.hOcc 141
  · exact hroot.hOcc 236
  · exact hroot.hOcc 405
  · exact hroot.hOcc 436
  · exact hroot.hOcc 581
  · exact hroot.hOcc 724
  · exact hroot.hOcc 728
  · exact hroot.hOcc 742
  · exact hroot.hOcc 758
  · exact hroot.hOcc 761
  · exact hroot.hOcc 774
  · exact hroot.hOcc 823
  · exact hroot.hOcc 887
  · exact hroot.hOcc 1122
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1375
  · exact hroot.hOcc 1376
  · exact hroot.hOcc 1397
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1439
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1537
  · exact hroot.hOcc 1651
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37

end QiushiMatmul
