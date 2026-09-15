import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0218Refs : Fin 42 → RowRef 1665 43 := ![.occ 139, .occ 145, .occ 220, .occ 226, .occ 290, .occ 379, .occ 396, .occ 551, .occ 556, .occ 708, .occ 1116, .occ 1159, .occ 1174, .occ 1220, .occ 1222, .occ 1258, .occ 1287, .occ 1328, .occ 1331, .occ 1345, .occ 1347, .occ 1388, .occ 1426, .occ 1462, .occ 1470, .occ 1471, .occ 1481, .occ 1540, .occ 1548, .occ 1606, .occ 1628, .occ 1653, .occ 1662, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchGe 16 (1), .branchGe 37 (1), .branchLe 17 (0), .branchLe 41 (0)]

def plane484GenLeaf0218Mult : Fin 42 → Nat := ![318, 40, 20, 14, 2, 138, 14, 86, 74, 86, 14, 151, 74, 34, 253, 130, 60, 82, 10, 10, 81, 15, 45, 10, 42, 16, 176, 112, 120, 34, 23, 29, 151, 512, 210, 336, 838, 878, 1688, 496, 336, 512]

theorem plane484GenLeaf0218 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0218Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0218Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0218Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0218Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 139
  · exact hroot.hOcc 145
  · exact hroot.hOcc 220
  · exact hroot.hOcc 226
  · exact hroot.hOcc 290
  · exact hroot.hOcc 379
  · exact hroot.hOcc 396
  · exact hroot.hOcc 551
  · exact hroot.hOcc 556
  · exact hroot.hOcc 708
  · exact hroot.hOcc 1116
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1287
  · exact hroot.hOcc 1328
  · exact hroot.hOcc 1331
  · exact hroot.hOcc 1345
  · exact hroot.hOcc 1347
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1462
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1540
  · exact hroot.hOcc 1548
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1653
  · exact hroot.hOcc 1662
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41

end QiushiMatmul
