import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0009Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 123, .occ 125, .occ 127, .occ 128, .occ 132, .occ 257, .occ 258, .occ 330, .occ 385, .occ 566, .occ 686, .occ 687, .occ 1146, .occ 1148, .occ 1186, .occ 1216, .occ 1231, .occ 1272, .occ 1281, .occ 1335, .occ 1357, .occ 1423, .occ 1470, .occ 1489, .occ 1589, .occ 1608, .occ 1621, .occ 1626, .occ 1647, .occ 1664, .sumGe, .nonneg 2, .nonneg 5, .branchLe 15 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchLe 41 (0), .branchGe 8 (1), .branchGe 9 (1), .branchGe 40 (1)]

def plane484GenLeaf0009Mult : Fin 44 → Nat := ![541, 2481, 3939, 46, 2227, 55, 370, 71, 115, 1860, 1393, 1692, 720, 1381, 13, 2072, 1086, 345, 318, 685, 154, 361, 127, 547, 3734, 2906, 2978, 313, 1937, 284, 213, 7599, 6292, 817, 6958, 6513, 2860, 4805, 5323, 7238, 5527, 13280, 13529, 10351]

theorem plane484GenLeaf0009 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_40 : (1 : Int) ≤ x 40)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0009Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0009Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0009Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0009Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 330
  · exact hroot.hOcc 385
  · exact hroot.hOcc 566
  · exact hroot.hOcc 686
  · exact hroot.hOcc 687
  · exact hroot.hOcc 1146
  · exact hroot.hOcc 1148
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1231
  · exact hroot.hOcc 1272
  · exact hroot.hOcc 1281
  · exact hroot.hOcc 1335
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1423
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1589
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1621
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1647
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (9 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (40 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_40

end QiushiMatmul
