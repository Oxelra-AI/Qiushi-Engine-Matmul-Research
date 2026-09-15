import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0013Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 132, .occ 139, .occ 140, .occ 142, .occ 492, .occ 499, .occ 726, .occ 796, .occ 1140, .occ 1168, .occ 1318, .occ 1336, .occ 1353, .occ 1369, .occ 1399, .occ 1403, .occ 1422, .occ 1429, .occ 1433, .occ 1434, .occ 1454, .occ 1458, .occ 1479, .occ 1489, .occ 1607, .occ 1626, .occ 1628, .occ 1655, .occ 1659, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchGe 41 (1), .branchLe 19 (0), .branchGe 42 (1), .branchLe 7 (0), .branchLe 31 (0), .branchLe 14 (0)]

def plane484GenLeaf0013Mult : Fin 44 → Nat := ![44754, 12523, 63448, 36404, 13329, 13766, 33782, 4647, 127764, 68336, 77221, 12667, 535, 7503, 42855, 18177, 22633, 13626, 11546, 9657, 104910, 4921, 50060, 2494, 15365, 61027, 58032, 22960, 37452, 6765, 281154, 207068, 265789, 205315, 273739, 192973, 174195, 208581, 71567, 185089, 238253, 197167, 208574, 230076]

theorem plane484GenLeaf0013 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0013Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0013Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0013Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0013Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 132
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 492
  · exact hroot.hOcc 499
  · exact hroot.hOcc 726
  · exact hroot.hOcc 796
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1318
  · exact hroot.hOcc 1336
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1369
  · exact hroot.hOcc 1399
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1429
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1434
  · exact hroot.hOcc 1454
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1479
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1607
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
