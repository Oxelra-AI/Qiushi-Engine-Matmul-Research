import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0197Refs : Fin 44 → RowRef 1665 43 := ![.occ 121, .occ 127, .occ 128, .occ 141, .occ 196, .occ 216, .occ 390, .occ 1140, .occ 1160, .occ 1166, .occ 1179, .occ 1205, .occ 1214, .occ 1216, .occ 1235, .occ 1241, .occ 1259, .occ 1287, .occ 1357, .occ 1436, .occ 1459, .occ 1467, .occ 1472, .occ 1478, .occ 1496, .occ 1556, .occ 1597, .occ 1601, .occ 1606, .occ 1618, .occ 1620, .occ 1627, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchGe 1 (1), .branchLe 22 (0), .branchLe 21 (0), .branchLe 6 (0), .branchLe 38 (0)]

def plane484GenLeaf0197Mult : Fin 44 → Nat := ![26086, 291772, 212152, 224780, 100860, 38004, 146840, 23877, 9731, 50205, 54786, 156415, 248061, 26259, 39818, 66332, 110710, 75420, 181877, 10226, 175264, 72572, 185150, 23392, 75108, 19002, 7576, 63583, 35364, 49496, 6729, 7365, 648024, 286520, 572916, 564368, 900698, 572604, 357288, 836444, 593390, 455298, 332860, 543102]

theorem plane484GenLeaf0197 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_21 : x 21 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0197Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0197Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0197Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0197Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 127
  · exact hroot.hOcc 128
  · exact hroot.hOcc 141
  · exact hroot.hOcc 196
  · exact hroot.hOcc 216
  · exact hroot.hOcc 390
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1235
  · exact hroot.hOcc 1241
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1287
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1436
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1556
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1601
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1627
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (21 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_21
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (38 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38

end QiushiMatmul
