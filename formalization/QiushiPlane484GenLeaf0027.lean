import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0027Refs : Fin 44 → RowRef 1665 43 := ![.occ 105, .occ 120, .occ 142, .occ 713, .occ 774, .occ 776, .occ 787, .occ 800, .occ 803, .occ 1150, .occ 1170, .occ 1174, .occ 1186, .occ 1187, .occ 1205, .occ 1277, .occ 1278, .occ 1281, .occ 1334, .occ 1377, .occ 1412, .occ 1426, .occ 1470, .occ 1471, .occ 1472, .occ 1489, .occ 1608, .occ 1617, .occ 1627, .occ 1659, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchLe 25 (0), .branchLe 18 (0), .branchGe 42 (1), .branchLe 23 (0), .branchLe 14 (0), .branchLe 24 (0)]

def plane484GenLeaf0027Mult : Fin 44 → Nat := ![81, 1644, 197, 1574, 4802, 53, 2961, 1093, 1682, 1564, 3368, 804, 737, 737, 15, 439, 1285, 411, 1232, 1235, 2018, 872, 1793, 96, 4262, 263, 2759, 1718, 2545, 1393, 11079, 2744, 9342, 10983, 7797, 7299, 8519, 20022, 3727, 8386, 18322, 7750, 8189, 8123]

theorem plane484GenLeaf0027 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_24 : x 24 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0027Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0027Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0027Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0027Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 105
  · exact hroot.hOcc 120
  · exact hroot.hOcc 142
  · exact hroot.hOcc 713
  · exact hroot.hOcc 774
  · exact hroot.hOcc 776
  · exact hroot.hOcc 787
  · exact hroot.hOcc 800
  · exact hroot.hOcc 803
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1170
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1186
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1277
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1281
  · exact hroot.hOcc 1334
  · exact hroot.hOcc 1377
  · exact hroot.hOcc 1412
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1617
  · exact hroot.hOcc 1627
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (24 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_24

end QiushiMatmul
