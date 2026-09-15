import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0341Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 123, .occ 138, .occ 139, .occ 141, .occ 238, .occ 350, .occ 406, .occ 816, .occ 1101, .occ 1136, .occ 1147, .occ 1154, .occ 1196, .occ 1214, .occ 1319, .occ 1452, .occ 1458, .occ 1470, .occ 1471, .occ 1483, .occ 1491, .occ 1500, .occ 1504, .occ 1516, .occ 1517, .occ 1573, .occ 1580, .sumGe, .nonneg 15, .nonneg 16, .nonneg 17, .nonneg 19, .nonneg 23, .branchGe 2 (1), .branchLe 7 (0), .branchGe 26 (1), .branchLe 14 (0), .branchGe 1 (1), .branchGe 30 (1), .branchGe 36 (1), .branchGe 18 (1)]

def plane484GenLeaf0341Mult : Fin 43 → Nat := ![855, 981, 2788, 9223, 6545, 6319, 2450, 2948, 953, 1595, 1139, 2107, 1430, 58, 1858, 293, 1035, 888, 2238, 1430, 3194, 807, 724, 963, 1540, 878, 1046, 5305, 841, 9281, 749, 1888, 191, 17232, 8915, 12854, 6284, 28695, 8440, 7438, 15531, 17827, 28596]

theorem plane484GenLeaf0341 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_36 : (1 : Int) ≤ x 36)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_26 : (1 : Int) ≤ x 26)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0341Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0341Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0341Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0341Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 123
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 238
  · exact hroot.hOcc 350
  · exact hroot.hOcc 406
  · exact hroot.hOcc 816
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1136
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1319
  · exact hroot.hOcc 1452
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1500
  · exact hroot.hOcc 1504
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1573
  · exact hroot.hOcc 1580
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 15
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 17
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_26
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (36 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_36
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18

end QiushiMatmul
