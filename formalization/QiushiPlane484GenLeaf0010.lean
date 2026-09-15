import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0010Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 122, .occ 126, .occ 140, .occ 145, .occ 366, .occ 501, .occ 536, .occ 695, .occ 1147, .occ 1150, .occ 1166, .occ 1174, .occ 1289, .occ 1301, .occ 1307, .occ 1316, .occ 1321, .occ 1325, .occ 1351, .occ 1353, .occ 1357, .occ 1477, .occ 1489, .occ 1508, .occ 1520, .occ 1580, .occ 1608, .occ 1626, .occ 1634, .occ 1655, .occ 1657, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchGe 41 (1), .branchLe 19 (0), .branchLe 42 (0), .branchLe 38 (0)]

def plane484GenLeaf0010Mult : Fin 44 → Nat := ![3059030, 1056523, 296371, 806145, 167418, 2088516, 51186, 185910, 220035, 547609, 440751, 1653634, 167474, 81069, 470259, 398719, 995755, 625838, 2617192, 1702865, 396321, 855776, 475158, 945885, 365794, 172499, 2183069, 2044849, 194726, 1407116, 3590728, 1740422, 10460270, 7393110, 7263289, 8410315, 8239351, 6041732, 7027726, 6456956, 1526989, 10019519, 5587262, 10460270]

theorem plane484GenLeaf0010 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_41 : (1 : Int) ≤ x 41)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0010Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0010Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 122
  · exact hroot.hOcc 126
  · exact hroot.hOcc 140
  · exact hroot.hOcc 145
  · exact hroot.hOcc 366
  · exact hroot.hOcc 501
  · exact hroot.hOcc 536
  · exact hroot.hOcc 695
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1289
  · exact hroot.hOcc 1301
  · exact hroot.hOcc 1307
  · exact hroot.hOcc 1316
  · exact hroot.hOcc 1321
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1351
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1477
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1508
  · exact hroot.hOcc 1520
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1634
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1657
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
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38

end QiushiMatmul
