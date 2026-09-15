import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0003Refs : Fin 43 → RowRef 1665 43 := ![.occ 120, .occ 128, .occ 133, .occ 134, .occ 139, .occ 262, .occ 452, .occ 682, .occ 771, .occ 781, .occ 1147, .occ 1150, .occ 1196, .occ 1229, .occ 1231, .occ 1233, .occ 1257, .occ 1323, .occ 1329, .occ 1357, .occ 1376, .occ 1423, .occ 1424, .occ 1462, .occ 1500, .occ 1502, .occ 1504, .occ 1554, .occ 1608, .occ 1626, .occ 1628, .occ 1647, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchLe 41 (0), .branchLe 8 (0), .branchGe 10 (1)]

def plane484GenLeaf0003Mult : Fin 43 → Nat := ![45220, 4797, 13493, 34064, 3856, 1216, 10930, 12563, 17044, 2043, 7185, 1889, 33592, 6305, 22613, 3040, 1051, 4819, 1946, 7163, 1762, 8311, 14152, 16706, 1350, 126, 447, 4214, 14787, 21975, 14340, 4188, 89145, 53249, 44180, 89145, 87256, 71992, 49363, 77592, 89145, 69561, 119037]

theorem plane484GenLeaf0003 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0003Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0003Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0003Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0003Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 128
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 262
  · exact hroot.hOcc 452
  · exact hroot.hOcc 682
  · exact hroot.hOcc 771
  · exact hroot.hOcc 781
  · exact hroot.hOcc 1147
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1229
  · exact hroot.hOcc 1231
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1257
  · exact hroot.hOcc 1323
  · exact hroot.hOcc 1329
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1376
  · exact hroot.hOcc 1423
  · exact hroot.hOcc 1424
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1500
  · exact hroot.hOcc 1502
  · exact hroot.hOcc 1504
  · exact hroot.hOcc 1554
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1647
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
