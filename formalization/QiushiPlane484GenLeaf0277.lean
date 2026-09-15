import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0277Refs : Fin 42 → RowRef 1665 43 := ![.occ 112, .occ 120, .occ 127, .occ 130, .occ 180, .occ 228, .occ 519, .occ 556, .occ 688, .occ 767, .occ 1154, .occ 1180, .occ 1186, .occ 1187, .occ 1190, .occ 1196, .occ 1332, .occ 1390, .occ 1391, .occ 1419, .occ 1467, .occ 1491, .occ 1516, .occ 1590, .occ 1603, .occ 1620, .occ 1639, .occ 1640, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchLe 13 (0), .branchGe 37 (1), .branchLe 32 (0), .branchLe 8 (0), .branchGe 9 (1), .branchGe 41 (1)]

def plane484GenLeaf0277Mult : Fin 42 → Nat := ![119, 71, 18, 77, 54, 77, 54, 45, 50, 39, 11, 44, 53, 40, 11, 11, 17, 22, 75, 49, 7, 22, 79, 70, 11, 66, 5, 5, 225, 143, 20, 119, 220, 154, 334, 225, 22, 172, 225, 68, 748, 251]

theorem plane484GenLeaf0277 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0277Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0277Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0277Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0277Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 112
  · exact hroot.hOcc 120
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 180
  · exact hroot.hOcc 228
  · exact hroot.hOcc 519
  · exact hroot.hOcc 556
  · exact hroot.hOcc 688
  · exact hroot.hOcc 767
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1180
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1332
  · exact hroot.hOcc 1390
  · exact hroot.hOcc 1391
  · exact hroot.hOcc 1419
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1640
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41

end QiushiMatmul
