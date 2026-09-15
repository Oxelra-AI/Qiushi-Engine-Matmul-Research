import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0219Refs : Fin 44 → RowRef 1665 43 := ![.occ 139, .occ 142, .occ 220, .occ 379, .occ 390, .occ 472, .occ 473, .occ 506, .occ 551, .occ 556, .occ 671, .occ 1159, .occ 1168, .occ 1208, .occ 1222, .occ 1233, .occ 1236, .occ 1262, .occ 1287, .occ 1301, .occ 1341, .occ 1347, .occ 1358, .occ 1425, .occ 1426, .occ 1470, .occ 1519, .occ 1597, .occ 1606, .occ 1632, .occ 1639, .occ 1655, .occ 1656, .sumGe, .nonneg 24, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchGe 16 (1), .branchGe 37 (1), .branchLe 17 (0), .branchGe 41 (1), .branchLe 13 (0)]

def plane484GenLeaf0219Mult : Fin 44 → Nat := ![8774, 13848, 2012, 11123, 2012, 463, 84, 5209, 6759, 8066, 13687, 17466, 84, 7830, 4692, 42, 15550, 610, 11844, 2862, 1928, 8222, 874, 17765, 2438, 6458, 126, 42, 1928, 5611, 321, 1893, 3592, 34200, 1381, 2012, 33879, 60131, 95748, 141420, 3729, 31951, 10341, 34200]

theorem plane484GenLeaf0219 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0219Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0219Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0219Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0219Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 139
  · exact hroot.hOcc 142
  · exact hroot.hOcc 220
  · exact hroot.hOcc 379
  · exact hroot.hOcc 390
  · exact hroot.hOcc 472
  · exact hroot.hOcc 473
  · exact hroot.hOcc 506
  · exact hroot.hOcc 551
  · exact hroot.hOcc 556
  · exact hroot.hOcc 671
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1262
  · exact hroot.hOcc 1287
  · exact hroot.hOcc 1301
  · exact hroot.hOcc 1341
  · exact hroot.hOcc 1347
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1425
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1519
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1632
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (41 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_41
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13

end QiushiMatmul
