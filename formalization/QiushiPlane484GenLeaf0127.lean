import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0127Refs : Fin 44 → RowRef 1665 43 := ![.occ 95, .occ 128, .occ 141, .occ 175, .occ 452, .occ 517, .occ 750, .occ 770, .occ 772, .occ 775, .occ 801, .occ 831, .occ 1168, .occ 1252, .occ 1312, .occ 1370, .occ 1422, .occ 1428, .occ 1436, .occ 1458, .occ 1471, .occ 1600, .occ 1603, .occ 1606, .occ 1608, .occ 1620, .occ 1629, .occ 1630, .occ 1631, .occ 1636, .occ 1652, .occ 1659, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 39 (0), .branchLe 32 (0), .branchGe 28 (1), .branchLe 6 (0), .branchGe 42 (1), .branchGe 10 (1)]

def plane484GenLeaf0127Mult : Fin 44 → Nat := ![1326, 1732, 20, 414, 716, 1344, 264, 4524, 1404, 1990, 120, 1908, 22, 1090, 450, 1772, 402, 70, 1666, 190, 1718, 120, 1512, 698, 310, 1733, 1153, 141, 190, 31, 1091, 1386, 6215, 2254, 6184, 7340, 3784, 5684, 4328, 5040, 7956, 3548, 13446, 19398]

theorem plane484GenLeaf0127 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_39 : x 39 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0127Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0127Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0127Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0127Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 95
  · exact hroot.hOcc 128
  · exact hroot.hOcc 141
  · exact hroot.hOcc 175
  · exact hroot.hOcc 452
  · exact hroot.hOcc 517
  · exact hroot.hOcc 750
  · exact hroot.hOcc 770
  · exact hroot.hOcc 772
  · exact hroot.hOcc 775
  · exact hroot.hOcc 801
  · exact hroot.hOcc 831
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1252
  · exact hroot.hOcc 1312
  · exact hroot.hOcc 1370
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1436
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1600
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1631
  · exact hroot.hOcc 1636
  · exact hroot.hOcc 1652
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_39
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
