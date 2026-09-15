import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0446Refs : Fin 44 → RowRef 1665 43 := ![.occ 129, .occ 131, .occ 142, .occ 256, .occ 325, .occ 329, .occ 580, .occ 968, .occ 991, .occ 1147, .occ 1215, .occ 1250, .occ 1266, .occ 1297, .occ 1334, .occ 1350, .occ 1382, .occ 1386, .occ 1389, .occ 1393, .occ 1396, .occ 1458, .occ 1459, .occ 1524, .occ 1573, .occ 1580, .occ 1631, .occ 1639, .occ 1651, .sumGe, .nonneg 2, .nonneg 19, .nonneg 20, .nonneg 21, .nonneg 22, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchLe 29 (0), .branchGe 23 (1), .branchLe 10 (0), .branchLe 3 (0), .branchGe 26 (1)]

def plane484GenLeaf0446Mult : Fin 44 → Nat := ![4222, 15086, 14930, 320, 35821, 6725, 516, 4369, 7960, 2503, 1436, 8998, 2275, 3072, 5574, 5307, 10989, 498, 4204, 10905, 366, 3413, 3695, 417, 2305, 12505, 1751, 5439, 6296, 35821, 10247, 23562, 3270, 2535, 64379, 93746, 25667, 25479, 1583, 34385, 46003, 17455, 33318, 100293]

theorem plane484GenLeaf0446 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_23 : (1 : Int) ≤ x 23)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0446Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0446Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0446Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0446Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 129
  · exact hroot.hOcc 131
  · exact hroot.hOcc 142
  · exact hroot.hOcc 256
  · exact hroot.hOcc 325
  · exact hroot.hOcc 329
  · exact hroot.hOcc 580
  · exact hroot.hOcc 968
  · exact hroot.hOcc 991
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1250
  · exact hroot.hOcc 1266
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1350
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1386
  · exact hroot.hOcc 1389
  · exact hroot.hOcc 1393
  · exact hroot.hOcc 1396
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1651
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 20
  · change (∑ k, (if k = (21 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 21
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_23
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26

end QiushiMatmul
