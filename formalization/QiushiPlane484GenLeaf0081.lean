import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0081Refs : Fin 39 → RowRef 1665 43 := ![.occ 129, .occ 131, .occ 140, .occ 524, .occ 534, .occ 545, .occ 604, .occ 726, .occ 739, .occ 743, .occ 858, .occ 861, .occ 1170, .occ 1252, .occ 1301, .occ 1343, .occ 1378, .occ 1386, .occ 1402, .occ 1412, .occ 1433, .occ 1437, .occ 1458, .occ 1602, .occ 1621, .sumGe, .nonneg 0, .nonneg 1, .nonneg 15, .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchGe 42 (1), .branchLe 9 (0), .branchGe 20 (1), .branchGe 41 (1), .branchGe 24 (1), .branchLe 3 (0)]

def plane484GenLeaf0081Mult : Fin 39 → Nat := ![15, 13, 45, 26, 5, 16, 21, 25, 10, 4, 43, 19, 16, 21, 1, 4, 18, 6, 3, 6, 2, 2, 2, 12, 2, 45, 13, 21, 89, 2, 42, 3, 97, 45, 45, 176, 49, 143, 42]

theorem plane484GenLeaf0081 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0081Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0081Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0081Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0081Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 140
  · exact hroot.hOcc 524
  · exact hroot.hOcc 534
  · exact hroot.hOcc 545
  · exact hroot.hOcc 604
  · exact hroot.hOcc 726
  · exact hroot.hOcc 739
  · exact hroot.hOcc 743
  · exact hroot.hOcc 858
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1252
  · exact hroot.hOcc 1301
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1378
  · exact hroot.hOcc 1386
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1412
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1437
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1621
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3

end QiushiMatmul
