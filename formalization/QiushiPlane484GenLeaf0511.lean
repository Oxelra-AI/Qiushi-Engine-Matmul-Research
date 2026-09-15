import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0511Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 124, .occ 128, .occ 130, .occ 131, .occ 133, .occ 138, .occ 140, .occ 142, .occ 292, .occ 664, .occ 961, .occ 1159, .occ 1233, .occ 1265, .occ 1280, .occ 1314, .occ 1344, .occ 1349, .occ 1358, .occ 1388, .occ 1440, .occ 1471, .occ 1486, .occ 1534, .occ 1552, .occ 1609, .occ 1610, .occ 1632, .occ 1641, .occ 1661, .sumGe, .nonneg 0, .nonneg 12, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchLe 34 (0), .branchLe 8 (0), .branchLe 33 (0), .branchGe 5 (1), .branchGe 10 (1)]

def plane484GenLeaf0511Mult : Fin 44 → Nat := ![50574, 65918, 52934, 11748, 31255, 15195, 37944, 45071, 4479, 31868, 10880, 19778, 2808, 4958, 54854, 23086, 10006, 1290, 8736, 25316, 19002, 12124, 17736, 22582, 30340, 7486, 23592, 30876, 6314, 10806, 5024, 137250, 48422, 49296, 198240, 80692, 28830, 16334, 137250, 124436, 47578, 137250, 214480, 177510]

theorem plane484GenLeaf0511 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0511Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0511Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0511Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0511Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 133
  · exact hroot.hOcc 138
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 292
  · exact hroot.hOcc 664
  · exact hroot.hOcc 961
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1265
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1314
  · exact hroot.hOcc 1344
  · exact hroot.hOcc 1349
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1534
  · exact hroot.hOcc 1552
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1632
  · exact hroot.hOcc 1641
  · exact hroot.hOcc 1661
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (12 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 12
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
