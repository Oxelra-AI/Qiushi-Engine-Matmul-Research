import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0445Refs : Fin 44 → RowRef 1665 43 := ![.occ 131, .occ 138, .occ 329, .occ 627, .occ 693, .occ 1143, .occ 1150, .occ 1186, .occ 1188, .occ 1190, .occ 1200, .occ 1243, .occ 1256, .occ 1264, .occ 1270, .occ 1288, .occ 1333, .occ 1371, .occ 1379, .occ 1385, .occ 1386, .occ 1396, .occ 1456, .occ 1458, .occ 1483, .occ 1621, .occ 1624, .occ 1631, .occ 1642, .sumGe, .nonneg 18, .nonneg 19, .nonneg 20, .nonneg 25, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchLe 29 (0), .branchGe 23 (1), .branchLe 10 (0), .branchLe 3 (0), .branchLe 26 (0), .branchGe 30 (1)]

def plane484GenLeaf0445Mult : Fin 44 → Nat := ![16847, 37428, 45432, 5425, 2181, 2090, 9280, 5359, 7223, 20968, 6414, 9009, 9517, 10218, 25128, 18661, 19932, 7669, 2394, 4019, 10264, 8926, 10264, 12302, 11176, 28262, 614, 29656, 6012, 96670, 17060, 81606, 25495, 6892, 154506, 54730, 29732, 50947, 96670, 158370, 81141, 96670, 53230, 136033]

theorem plane484GenLeaf0445 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0445Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0445Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0445Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0445Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 131
  · exact hroot.hOcc 138
  · exact hroot.hOcc 329
  · exact hroot.hOcc 627
  · exact hroot.hOcc 693
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1243
  · exact hroot.hOcc 1256
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1288
  · exact hroot.hOcc 1333
  · exact hroot.hOcc 1371
  · exact hroot.hOcc 1379
  · exact hroot.hOcc 1385
  · exact hroot.hOcc 1386
  · exact hroot.hOcc 1396
  · exact hroot.hOcc 1456
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1621
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1642
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 18
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30

end QiushiMatmul
