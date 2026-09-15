import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0062Refs : Fin 43 → RowRef 1665 43 := ![.occ 123, .occ 134, .occ 135, .occ 140, .occ 141, .occ 386, .occ 414, .occ 436, .occ 708, .occ 823, .occ 1172, .occ 1173, .occ 1220, .occ 1279, .occ 1307, .occ 1318, .occ 1322, .occ 1331, .occ 1336, .occ 1386, .occ 1418, .occ 1459, .occ 1489, .occ 1510, .occ 1512, .occ 1524, .occ 1534, .occ 1648, .occ 1657, .occ 1658, .sumGe, .nonneg 0, .nonneg 17, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchLe 42 (0), .branchLe 10 (0), .branchGe 20 (1), .branchGe 40 (1), .branchLe 28 (0)]

def plane484GenLeaf0062Mult : Fin 43 → Nat := ![738, 1410, 170, 1822, 902, 926, 360, 1119, 1397, 1688, 698, 72, 2773, 79, 648, 230, 295, 38, 1140, 546, 135, 313, 969, 140, 1065, 1039, 563, 380, 1335, 457, 5337, 505, 892, 1518, 2154, 5337, 5337, 2584, 3374, 4878, 11205, 6922, 5337]

theorem plane484GenLeaf0062 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hLB_20 : (1 : Int) ≤ x 20)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0062Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0062Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0062Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0062Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 134
  · exact hroot.hOcc 135
  · exact hroot.hOcc 140
  · exact hroot.hOcc 141
  · exact hroot.hOcc 386
  · exact hroot.hOcc 414
  · exact hroot.hOcc 436
  · exact hroot.hOcc 708
  · exact hroot.hOcc 823
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1279
  · exact hroot.hOcc 1307
  · exact hroot.hOcc 1318
  · exact hroot.hOcc 1322
  · exact hroot.hOcc 1331
  · exact hroot.hOcc 1336
  · exact hroot.hOcc 1386
  · exact hroot.hOcc 1418
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1510
  · exact hroot.hOcc 1512
  · exact hroot.hOcc 1524
  · exact hroot.hOcc 1534
  · exact hroot.hOcc 1648
  · exact hroot.hOcc 1657
  · exact hroot.hOcc 1658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (20 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_20
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28

end QiushiMatmul
