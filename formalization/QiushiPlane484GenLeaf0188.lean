import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0188Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 129, .occ 197, .occ 201, .occ 242, .occ 344, .occ 376, .occ 390, .occ 470, .occ 706, .occ 789, .occ 803, .occ 1143, .occ 1145, .occ 1151, .occ 1179, .occ 1214, .occ 1233, .occ 1234, .occ 1259, .occ 1313, .occ 1314, .occ 1326, .occ 1373, .occ 1445, .occ 1472, .occ 1496, .occ 1505, .occ 1602, .occ 1620, .occ 1628, .occ 1658, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchLe 1 (0), .branchGe 5 (1), .branchLe 22 (0), .branchLe 30 (0), .branchLe 8 (0)]

def plane484GenLeaf0188Mult : Fin 44 → Nat := ![2339, 1262, 392, 2547, 1440, 1458, 2143, 1219, 2197, 1178, 57, 775, 1123, 241, 195, 671, 125, 157, 507, 505, 364, 429, 211, 929, 997, 392, 1240, 677, 195, 888, 99, 681, 4684, 4003, 2080, 13105, 11049, 4585, 2036, 2521, 11510, 4684, 4684, 3422]

theorem plane484GenLeaf0188 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_5 : (1 : Int) ≤ x 5)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0188Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0188Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0188Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0188Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 129
  · exact hroot.hOcc 197
  · exact hroot.hOcc 201
  · exact hroot.hOcc 242
  · exact hroot.hOcc 344
  · exact hroot.hOcc 376
  · exact hroot.hOcc 390
  · exact hroot.hOcc 470
  · exact hroot.hOcc 706
  · exact hroot.hOcc 789
  · exact hroot.hOcc 803
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1179
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1233
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1313
  · exact hroot.hOcc 1314
  · exact hroot.hOcc 1326
  · exact hroot.hOcc 1373
  · exact hroot.hOcc 1445
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1505
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1658
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_5
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8

end QiushiMatmul
