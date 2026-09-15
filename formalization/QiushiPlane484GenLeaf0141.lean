import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0141Refs : Fin 43 → RowRef 1665 43 := ![.occ 133, .occ 134, .occ 179, .occ 309, .occ 316, .occ 457, .occ 462, .occ 553, .occ 692, .occ 745, .occ 789, .occ 1140, .occ 1151, .occ 1216, .occ 1248, .occ 1283, .occ 1290, .occ 1307, .occ 1337, .occ 1370, .occ 1394, .occ 1436, .occ 1491, .occ 1526, .occ 1551, .occ 1580, .occ 1601, .occ 1629, .occ 1633, .occ 1637, .occ 1655, .occ 1656, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchLe 35 (0), .branchLe 7 (0), .branchGe 39 (1), .branchLe 16 (0), .branchLe 27 (0), .branchLe 13 (0), .branchLe 0 (0)]

def plane484GenLeaf0141Mult : Fin 43 → Nat := ![12, 236, 330, 1483, 1130, 380, 813, 1053, 359, 216, 78, 1057, 350, 242, 1267, 1029, 483, 118, 908, 733, 249, 726, 822, 65, 109, 124, 273, 415, 3, 176, 3, 1164, 3691, 2836, 2690, 11889, 3691, 3358, 7410, 2223, 3688, 2692, 3176]

theorem plane484GenLeaf0141 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0141Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0141Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0141Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0141Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 179
  · exact hroot.hOcc 309
  · exact hroot.hOcc 316
  · exact hroot.hOcc 457
  · exact hroot.hOcc 462
  · exact hroot.hOcc 553
  · exact hroot.hOcc 692
  · exact hroot.hOcc 745
  · exact hroot.hOcc 789
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1248
  · exact hroot.hOcc 1283
  · exact hroot.hOcc 1290
  · exact hroot.hOcc 1307
  · exact hroot.hOcc 1337
  · exact hroot.hOcc 1370
  · exact hroot.hOcc 1394
  · exact hroot.hOcc 1436
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1526
  · exact hroot.hOcc 1551
  · exact hroot.hOcc 1580
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1633
  · exact hroot.hOcc 1637
  · exact hroot.hOcc 1655
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
