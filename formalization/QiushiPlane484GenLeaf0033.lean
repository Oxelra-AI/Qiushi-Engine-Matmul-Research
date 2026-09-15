import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0033Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 290, .occ 455, .occ 533, .occ 534, .occ 555, .occ 623, .occ 671, .occ 733, .occ 749, .occ 977, .occ 1084, .occ 1170, .occ 1174, .occ 1220, .occ 1233, .occ 1247, .occ 1274, .occ 1279, .occ 1286, .occ 1353, .occ 1368, .occ 1384, .occ 1412, .occ 1429, .occ 1500, .occ 1508, .occ 1515, .occ 1602, .occ 1607, .occ 1663, .sumGe, .nonneg 19, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchLe 25 (0), .branchGe 18 (1), .branchLe 1 (0), .branchGe 11 (1)]

def plane484GenLeaf0033Mult : Fin 44 → Nat := ![1302, 340, 2002, 1512, 120, 74, 1243, 1137, 603, 983, 1477, 806, 169, 28, 477, 1292, 101, 981, 306, 129, 306, 289, 102, 306, 311, 1630, 5, 1489, 28, 283, 792, 3697, 102, 3391, 3697, 3391, 696, 3669, 2616, 9676, 3414, 7635, 3669, 11930]

theorem plane484GenLeaf0033 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0033Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0033Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0033Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0033Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 290
  · exact hroot.hOcc 455
  · exact hroot.hOcc 533
  · exact hroot.hOcc 534
  · exact hroot.hOcc 555
  · exact hroot.hOcc 623
  · exact hroot.hOcc 671
  · exact hroot.hOcc 733
  · exact hroot.hOcc 749
  · exact hroot.hOcc 977
  · exact hroot.hOcc 1084
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1247
  · exact hroot.hOcc 1274
  · exact hroot.hOcc 1279
  · exact hroot.hOcc 1286
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1368
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1412
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1500
  · exact hroot.hOcc 1508
  · exact hroot.hOcc 1515
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
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
  · change (∑ k, (if k = (11 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11

end QiushiMatmul
