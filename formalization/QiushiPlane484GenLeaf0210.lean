import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0210Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 128, .occ 216, .occ 383, .occ 390, .occ 438, .occ 454, .occ 465, .occ 470, .occ 520, .occ 670, .occ 707, .occ 716, .occ 727, .occ 774, .occ 1154, .occ 1160, .occ 1174, .occ 1224, .occ 1233, .occ 1383, .occ 1391, .occ 1420, .occ 1427, .occ 1459, .occ 1462, .occ 1467, .occ 1471, .occ 1499, .occ 1516, .occ 1606, .occ 1623, .occ 1649, .occ 1653, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchGe 18 (1), .branchLe 38 (0), .branchGe 37 (1), .branchLe 21 (0)]

def plane484GenLeaf0210Mult : Fin 44 → Nat := ![713, 152, 214, 2542, 996, 460, 322, 462, 2134, 785, 1916, 785, 134, 485, 567, 391, 458, 621, 681, 564, 170, 117, 165, 92, 513, 257, 271, 82, 1273, 180, 363, 1610, 215, 1, 3216, 2945, 3216, 10746, 8802, 2132, 10028, 2456, 4294, 2919]

theorem plane484GenLeaf0210 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_18 : (1 : Int) ≤ x 18)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0210Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0210Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0210Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0210Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 128
  · exact hroot.hOcc 216
  · exact hroot.hOcc 383
  · exact hroot.hOcc 390
  · exact hroot.hOcc 438
  · exact hroot.hOcc 454
  · exact hroot.hOcc 465
  · exact hroot.hOcc 470
  · exact hroot.hOcc 520
  · exact hroot.hOcc 670
  · exact hroot.hOcc 707
  · exact hroot.hOcc 716
  · exact hroot.hOcc 727
  · exact hroot.hOcc 774
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1224
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1383
  · exact hroot.hOcc 1391
  · exact hroot.hOcc 1420
  · exact hroot.hOcc 1427
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1499
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1623
  · exact hroot.hOcc 1649
  · exact hroot.hOcc 1653
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_18
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21

end QiushiMatmul
