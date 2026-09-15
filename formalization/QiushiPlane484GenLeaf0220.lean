import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0220Refs : Fin 44 → RowRef 1665 43 := ![.occ 129, .occ 220, .occ 528, .occ 549, .occ 569, .occ 570, .occ 603, .occ 632, .occ 671, .occ 937, .occ 938, .occ 1080, .occ 1124, .occ 1166, .occ 1172, .occ 1173, .occ 1301, .occ 1315, .occ 1353, .occ 1380, .occ 1391, .occ 1419, .occ 1534, .occ 1540, .occ 1584, .occ 1597, .occ 1601, .occ 1632, .occ 1643, .occ 1649, .occ 1657, .sumGe, .nonneg 4, .nonneg 22, .nonneg 24, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchGe 16 (1), .branchGe 37 (1), .branchLe 17 (0), .branchGe 41 (1), .branchGe 13 (1)]

def plane484GenLeaf0220Mult : Fin 44 → Nat := ![10, 1, 10, 11, 5, 11, 22, 3, 8, 16, 5, 19, 1, 5, 1, 6, 3, 7, 1, 8, 7, 6, 2, 3, 13, 6, 5, 2, 4, 5, 1, 28, 1, 8, 1, 28, 24, 77, 93, 93, 44, 24, 33, 132]

theorem plane484GenLeaf0220 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0220Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0220Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0220Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0220Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 129
  · exact hroot.hOcc 220
  · exact hroot.hOcc 528
  · exact hroot.hOcc 549
  · exact hroot.hOcc 569
  · exact hroot.hOcc 570
  · exact hroot.hOcc 603
  · exact hroot.hOcc 632
  · exact hroot.hOcc 671
  · exact hroot.hOcc 937
  · exact hroot.hOcc 938
  · exact hroot.hOcc 1080
  · exact hroot.hOcc 1124
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1301
  · exact hroot.hOcc 1315
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1380
  · exact hroot.hOcc 1391
  · exact hroot.hOcc 1419
  · exact hroot.hOcc 1534
  · exact hroot.hOcc 1540
  · exact hroot.hOcc 1584
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1632
  · exact hroot.hOcc 1643
  · exact hroot.hOcc 1649
  · exact hroot.hOcc 1657
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13

end QiushiMatmul
