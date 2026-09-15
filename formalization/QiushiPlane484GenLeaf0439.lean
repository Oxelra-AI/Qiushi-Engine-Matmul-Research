import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0439Refs : Fin 41 → RowRef 1665 43 := ![.occ 123, .occ 133, .occ 136, .occ 355, .occ 410, .occ 416, .occ 574, .occ 612, .occ 693, .occ 821, .occ 958, .occ 1334, .occ 1384, .occ 1390, .occ 1400, .occ 1416, .occ 1423, .occ 1433, .occ 1483, .occ 1502, .occ 1506, .occ 1518, .occ 1562, .occ 1596, .occ 1609, .occ 1642, .occ 1644, .sumGe, .nonneg 1, .nonneg 23, .nonneg 25, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchLe 29 (0), .branchGe 19 (1), .branchLe 31 (0), .branchLe 20 (0), .branchGe 38 (1), .branchGe 17 (1)]

def plane484GenLeaf0439Mult : Fin 41 → Nat := ![24, 1948, 1213, 729, 592, 12, 128, 209, 85, 989, 507, 80, 462, 427, 35, 82, 497, 83, 56, 282, 13, 670, 610, 624, 306, 510, 145, 1948, 624, 510, 3078, 1355, 1044, 1438, 1642, 1948, 5591, 1866, 1666, 4436, 6008]

theorem plane484GenLeaf0439 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0439Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0439Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0439Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0439Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 133
  · exact hroot.hOcc 136
  · exact hroot.hOcc 355
  · exact hroot.hOcc 410
  · exact hroot.hOcc 416
  · exact hroot.hOcc 574
  · exact hroot.hOcc 612
  · exact hroot.hOcc 693
  · exact hroot.hOcc 821
  · exact hroot.hOcc 958
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1384
  · exact hroot.hOcc 1390
  · exact hroot.hOcc 1400
  · exact hroot.hOcc 1416
  · exact hroot.hOcc 1423
  · exact hroot.hOcc 1433
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1502
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1518
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1596
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1642
  · exact hroot.hOcc 1644
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (31 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (38 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17

end QiushiMatmul
