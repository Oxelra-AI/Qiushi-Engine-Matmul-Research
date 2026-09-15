import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0126Refs : Fin 44 → RowRef 1665 43 := ![.occ 128, .occ 129, .occ 130, .occ 134, .occ 139, .occ 719, .occ 760, .occ 789, .occ 790, .occ 791, .occ 808, .occ 1042, .occ 1101, .occ 1145, .occ 1215, .occ 1251, .occ 1315, .occ 1343, .occ 1370, .occ 1372, .occ 1382, .occ 1427, .occ 1443, .occ 1446, .occ 1452, .occ 1472, .occ 1516, .occ 1603, .occ 1610, .occ 1619, .sumGe, .nonneg 11, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchLe 32 (0), .branchGe 28 (1), .branchLe 6 (0), .branchGe 42 (1), .branchLe 10 (0), .branchGe 5 (1)]

def plane484GenLeaf0126Mult : Fin 44 → Nat := ![590, 637, 190, 366, 5, 20, 213, 1260, 197, 999, 399, 1048, 437, 555, 257, 74, 295, 143, 162, 245, 616, 97, 663, 13, 139, 424, 704, 503, 703, 46, 2079, 368, 1877, 1524, 3415, 951, 186, 2079, 1834, 3286, 739, 5622, 1179, 6641]

theorem plane484GenLeaf0126 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0126Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0126Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0126Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0126Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 128
  · exact hroot.hOcc 129
  · exact hroot.hOcc 130
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 719
  · exact hroot.hOcc 760
  · exact hroot.hOcc 789
  · exact hroot.hOcc 790
  · exact hroot.hOcc 791
  · exact hroot.hOcc 808
  · exact hroot.hOcc 1042
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1251
  · exact hroot.hOcc 1315
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1370
  · exact hroot.hOcc 1372
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1427
  · exact hroot.hOcc 1443
  · exact hroot.hOcc 1446
  · exact hroot.hOcc 1452
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1619
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 11
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5

end QiushiMatmul
