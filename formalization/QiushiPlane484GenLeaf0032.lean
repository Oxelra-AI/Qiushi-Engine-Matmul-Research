import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0032Refs : Fin 44 → RowRef 1665 43 := ![.occ 134, .occ 141, .occ 385, .occ 432, .occ 442, .occ 445, .occ 597, .occ 1091, .occ 1132, .occ 1158, .occ 1159, .occ 1174, .occ 1196, .occ 1208, .occ 1234, .occ 1264, .occ 1335, .occ 1346, .occ 1392, .occ 1426, .occ 1429, .occ 1430, .occ 1470, .occ 1500, .occ 1503, .occ 1515, .occ 1610, .occ 1624, .occ 1626, .occ 1655, .sumGe, .nonneg 19, .nonneg 23, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchLe 25 (0), .branchGe 18 (1), .branchLe 1 (0), .branchLe 11 (0)]

def plane484GenLeaf0032Mult : Fin 44 → Nat := ![1131, 15632, 2161, 4102, 9118, 1840, 32, 395, 3220, 1286, 1286, 5271, 3220, 5365, 11127, 4726, 142, 1529, 14742, 3220, 3983, 5436, 5323, 2493, 1475, 5690, 2466, 8795, 2485, 6907, 35170, 3220, 6440, 29378, 31950, 33884, 35170, 24846, 5792, 41862, 11500, 85356, 9012, 24502]

theorem plane484GenLeaf0032 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0032Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0032Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0032Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0032Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 134
  · exact hroot.hOcc 141
  · exact hroot.hOcc 385
  · exact hroot.hOcc 432
  · exact hroot.hOcc 442
  · exact hroot.hOcc 445
  · exact hroot.hOcc 597
  · exact hroot.hOcc 1091
  · exact hroot.hOcc 1132
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1335
  · exact hroot.hOcc 1346
  · exact hroot.hOcc 1392
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1500
  · exact hroot.hOcc 1503
  · exact hroot.hOcc 1515
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1655
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (11 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11

end QiushiMatmul
