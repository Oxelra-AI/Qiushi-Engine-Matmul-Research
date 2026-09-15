import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0213Refs : Fin 44 → RowRef 1665 43 := ![.occ 119, .occ 120, .occ 124, .occ 130, .occ 139, .occ 141, .occ 323, .occ 379, .occ 390, .occ 506, .occ 553, .occ 572, .occ 591, .occ 614, .occ 990, .occ 997, .occ 1159, .occ 1179, .occ 1208, .occ 1214, .occ 1216, .occ 1222, .occ 1236, .occ 1265, .occ 1287, .occ 1417, .occ 1471, .occ 1481, .occ 1516, .occ 1526, .occ 1533, .occ 1636, .occ 1643, .occ 1656, .occ 1662, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchGe 16 (1), .branchLe 37 (0), .branchLe 22 (0), .branchLe 27 (0)]

def plane484GenLeaf0213Mult : Fin 44 → Nat := ![128, 530, 338, 1180, 3368, 370, 792, 2750, 592, 2098, 364, 104, 408, 994, 242, 1106, 2636, 370, 900, 185, 666, 2897, 973, 296, 1187, 740, 1010, 3404, 185, 128, 1364, 356, 241, 324, 647, 6157, 1838, 824, 15796, 16854, 20876, 5510, 2910, 4828]

theorem plane484GenLeaf0213 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0213Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0213Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0213Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0213Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 120
  · exact hroot.hOcc 124
  · exact hroot.hOcc 130
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 323
  · exact hroot.hOcc 379
  · exact hroot.hOcc 390
  · exact hroot.hOcc 506
  · exact hroot.hOcc 553
  · exact hroot.hOcc 572
  · exact hroot.hOcc 591
  · exact hroot.hOcc 614
  · exact hroot.hOcc 990
  · exact hroot.hOcc 997
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1265
  · exact hroot.hOcc 1287
  · exact hroot.hOcc 1417
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1516
  · exact hroot.hOcc 1526
  · exact hroot.hOcc 1533
  · exact hroot.hOcc 1636
  · exact hroot.hOcc 1643
  · exact hroot.hOcc 1656
  · exact hroot.hOcc 1662
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27

end QiushiMatmul
