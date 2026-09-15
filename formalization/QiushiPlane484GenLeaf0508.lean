import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0508Refs : Fin 42 → RowRef 1665 43 := ![.occ 126, .occ 130, .occ 131, .occ 133, .occ 138, .occ 140, .occ 142, .occ 291, .occ 483, .occ 534, .occ 539, .occ 549, .occ 610, .occ 645, .occ 689, .occ 774, .occ 783, .occ 803, .occ 1048, .occ 1334, .occ 1397, .occ 1430, .occ 1440, .occ 1467, .occ 1484, .occ 1486, .occ 1615, .occ 1632, .occ 1640, .sumGe, .nonneg 6, .nonneg 26, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 30 (0), .branchLe 34 (0), .branchLe 8 (0), .branchLe 33 (0), .branchLe 5 (0), .branchGe 41 (1), .branchGe 42 (1)]

def plane484GenLeaf0508Mult : Fin 42 → Nat := ![88, 88, 137, 155, 60, 177, 29, 46, 74, 52, 138, 166, 64, 40, 36, 22, 208, 42, 110, 134, 88, 36, 4, 56, 218, 36, 222, 88, 74, 476, 32, 16, 1430, 606, 218, 476, 476, 366, 420, 402, 314, 654]

theorem plane484GenLeaf0508 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0508Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0508Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0508Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0508Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 126
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 291
  · exact hroot.hOcc 483
  · exact hroot.hOcc 534
  · exact hroot.hOcc 539
  · exact hroot.hOcc 549
  · exact hroot.hOcc 610
  · exact hroot.hOcc 645
  · exact hroot.hOcc 689
  · exact hroot.hOcc 774
  · exact hroot.hOcc 783
  · exact hroot.hOcc 803
  · exact hroot.hOcc 1048
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1397
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1632
  · exact hroot.hOcc 1640
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (6 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 6
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42

end QiushiMatmul
