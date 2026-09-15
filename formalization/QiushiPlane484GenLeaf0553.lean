import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0553Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 122, .occ 126, .occ 131, .occ 133, .occ 140, .occ 242, .occ 295, .occ 528, .occ 532, .occ 610, .occ 671, .occ 754, .occ 1124, .occ 1188, .occ 1213, .occ 1214, .occ 1220, .occ 1292, .occ 1310, .occ 1370, .occ 1391, .occ 1409, .occ 1425, .occ 1453, .occ 1457, .occ 1465, .occ 1480, .occ 1481, .occ 1603, .sumGe, .nonneg 13, .nonneg 19, .nonneg 20, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchGe 1 (1), .branchGe 11 (1), .branchLe 32 (0)]

def plane484GenLeaf0553Mult : Fin 43 → Nat := ![11, 3317, 3328, 368, 1103, 1830, 1518, 432, 3776, 550, 81, 1505, 1892, 100, 53, 2373, 197, 431, 1456, 53, 64, 459, 53, 80, 16, 437, 140, 197, 607, 481, 1259, 3829, 3247, 560, 1112, 9598, 5758, 959, 1443, 4736, 7182, 14101, 3348]

theorem plane484GenLeaf0553 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0553Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0553Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0553Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0553Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 126
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 140
  · exact hroot.hOcc 242
  · exact hroot.hOcc 295
  · exact hroot.hOcc 528
  · exact hroot.hOcc 532
  · exact hroot.hOcc 610
  · exact hroot.hOcc 671
  · exact hroot.hOcc 754
  · exact hroot.hOcc 1124
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1292
  · exact hroot.hOcc 1310
  · exact hroot.hOcc 1370
  · exact hroot.hOcc 1391
  · exact hroot.hOcc 1409
  · exact hroot.hOcc 1425
  · exact hroot.hOcc 1453
  · exact hroot.hOcc 1457
  · exact hroot.hOcc 1465
  · exact hroot.hOcc 1480
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1603
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 13
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32

end QiushiMatmul
