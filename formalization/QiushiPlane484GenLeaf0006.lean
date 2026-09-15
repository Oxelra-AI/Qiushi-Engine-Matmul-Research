import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0006Refs : Fin 44 → RowRef 1665 43 := ![.occ 122, .occ 126, .occ 129, .occ 133, .occ 139, .occ 141, .occ 145, .occ 257, .occ 300, .occ 565, .occ 566, .occ 662, .occ 791, .occ 950, .occ 955, .occ 993, .occ 1066, .occ 1223, .occ 1261, .occ 1284, .occ 1286, .occ 1323, .occ 1325, .occ 1353, .occ 1428, .occ 1472, .occ 1608, .occ 1621, .occ 1630, .occ 1655, .occ 1664, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchLe 35 (0), .branchLe 41 (0), .branchGe 8 (1), .branchLe 9 (0), .branchGe 19 (1), .branchGe 28 (1)]

def plane484GenLeaf0006Mult : Fin 44 → Nat := ![692, 223, 261, 489, 782, 732, 245, 3795, 1158, 1038, 206, 962, 955, 587, 261, 505, 93, 209, 81, 713, 702, 948, 244, 683, 339, 460, 1269, 666, 833, 1286, 686, 4542, 1868, 4319, 3859, 2414, 2923, 670, 4082, 3256, 8417, 4542, 7862, 10384]

theorem plane484GenLeaf0006 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_19 : (1 : Int) ≤ x 19)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0006Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0006Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 126
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 145
  · exact hroot.hOcc 257
  · exact hroot.hOcc 300
  · exact hroot.hOcc 565
  · exact hroot.hOcc 566
  · exact hroot.hOcc 662
  · exact hroot.hOcc 791
  · exact hroot.hOcc 950
  · exact hroot.hOcc 955
  · exact hroot.hOcc 993
  · exact hroot.hOcc 1066
  · exact hroot.hOcc 1223
  · exact hroot.hOcc 1261
  · exact hroot.hOcc 1284
  · exact hroot.hOcc 1286
  · exact hroot.hOcc 1323
  · exact hroot.hOcc 1325
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1621
  · exact hroot.hOcc 1630
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1664
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (9 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_19
  · change (∑ k, (if k = (28 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28

end QiushiMatmul
