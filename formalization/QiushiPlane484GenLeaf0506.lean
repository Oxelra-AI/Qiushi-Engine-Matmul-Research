import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0506Refs : Fin 44 → RowRef 1665 43 := ![.occ 126, .occ 127, .occ 130, .occ 131, .occ 133, .occ 135, .occ 136, .occ 138, .occ 140, .occ 366, .occ 367, .occ 394, .occ 426, .occ 610, .occ 676, .occ 957, .occ 1233, .occ 1265, .occ 1280, .occ 1297, .occ 1334, .occ 1467, .occ 1481, .occ 1484, .occ 1499, .occ 1548, .occ 1603, .occ 1615, .occ 1620, .occ 1638, .occ 1654, .occ 1661, .occ 1663, .sumGe, .nonneg 25, .branchGe 15 (1), .branchGe 35 (1), .branchLe 26 (0), .branchLe 30 (0), .branchLe 34 (0), .branchLe 8 (0), .branchLe 33 (0), .branchLe 5 (0), .branchLe 41 (0)]

def plane484GenLeaf0506Mult : Fin 44 → Nat := ![38219, 14085, 2997, 41634, 44080, 11532, 849, 3121, 60, 24833, 15153, 10003, 1595, 30931, 2241, 19818, 12284, 8954, 10410, 19157, 1477, 20794, 540, 53682, 14828, 5714, 3854, 24370, 5975, 423, 29347, 4496, 207, 108366, 4404, 250987, 33597, 12112, 78596, 108366, 107736, 87032, 98989, 102391]

theorem plane484GenLeaf0506 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0506Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0506Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0506Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0506Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 126
  · exact hroot.hOcc 127
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 366
  · exact hroot.hOcc 367
  · exact hroot.hOcc 394
  · exact hroot.hOcc 426
  · exact hroot.hOcc 610
  · exact hroot.hOcc 676
  · exact hroot.hOcc 957
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1265
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1297
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1499
  · exact hroot.hOcc 1548
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1654
  · exact hroot.hOcc 1661
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 25
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41

end QiushiMatmul
