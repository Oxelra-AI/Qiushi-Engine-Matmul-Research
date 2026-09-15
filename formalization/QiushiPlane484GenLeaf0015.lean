import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0015Refs : Fin 44 → RowRef 1665 43 := ![.occ 132, .occ 491, .occ 536, .occ 538, .occ 699, .occ 751, .occ 786, .occ 798, .occ 804, .occ 860, .occ 1005, .occ 1154, .occ 1168, .occ 1270, .occ 1301, .occ 1351, .occ 1357, .occ 1369, .occ 1382, .occ 1396, .occ 1434, .occ 1458, .occ 1471, .occ 1580, .occ 1602, .occ 1608, .occ 1655, .occ 1656, .occ 1657, .occ 1659, .occ 1661, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchGe 41 (1), .branchLe 19 (0), .branchGe 42 (1), .branchLe 7 (0), .branchGe 31 (1)]

def plane484GenLeaf0015Mult : Fin 44 → Nat := ![1298, 3165, 606, 874, 47, 3552, 3775, 7714, 2487, 859, 382, 1415, 2897, 832, 145, 691, 286, 1356, 335, 712, 1522, 614, 962, 3025, 2157, 911, 2370, 652, 775, 2246, 877, 10672, 8426, 10672, 7643, 9795, 6249, 8162, 9611, 11913, 7863, 18548, 8986, 22643]

theorem plane484GenLeaf0015 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0015Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0015Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0015Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0015Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 132
  · exact hroot.hOcc 491
  · exact hroot.hOcc 536
  · exact hroot.hOcc 538
  · exact hroot.hOcc 699
  · exact hroot.hOcc 751
  · exact hroot.hOcc 786
  · exact hroot.hOcc 798
  · exact hroot.hOcc 804
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1005
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1270
  · exact hroot.hOcc 1301
  · exact hroot.hOcc 1351
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1369
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1396
  · exact hroot.hOcc 1434
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1656
  · exact hroot.hOcc 1657
  · exact hroot.hOcc 1659
  · exact hroot.hOcc 1661
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
  · change (∑ k, (if k = (31 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31

end QiushiMatmul
