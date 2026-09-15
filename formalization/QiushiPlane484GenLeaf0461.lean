import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0461Refs : Fin 43 → RowRef 1665 43 := ![.occ 133, .occ 134, .occ 136, .occ 138, .occ 139, .occ 140, .occ 160, .occ 290, .occ 297, .occ 514, .occ 583, .occ 775, .occ 863, .occ 1101, .occ 1103, .occ 1159, .occ 1174, .occ 1191, .occ 1229, .occ 1268, .occ 1284, .occ 1285, .occ 1329, .occ 1330, .occ 1332, .occ 1344, .occ 1404, .occ 1554, .occ 1567, .occ 1590, .occ 1641, .occ 1656, .sumGe, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchGe 29 (1), .branchGe 27 (1), .branchLe 8 (0), .branchLe 4 (0), .branchGe 16 (1), .branchGe 10 (1)]

def plane484GenLeaf0461Mult : Fin 43 → Nat := ![731, 764, 709, 1939, 1177, 1024, 3042, 1346, 918, 1230, 1124, 5460, 1820, 140, 1598, 650, 214, 2210, 90, 978, 70, 70, 530, 2186, 608, 1050, 724, 1702, 140, 1300, 1186, 834, 6184, 10274, 5534, 2294, 2590, 11582, 7238, 5350, 3400, 15544, 15704]

theorem plane484GenLeaf0461 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_10 : (1 : Int) ≤ x 10)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0461Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0461Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0461Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0461Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 133
  · exact hroot.hOcc 134
  · exact hroot.hOcc 136
  · exact hroot.hOcc 138
  · exact hroot.hOcc 139
  · exact hroot.hOcc 140
  · exact hroot.hOcc 160
  · exact hroot.hOcc 290
  · exact hroot.hOcc 297
  · exact hroot.hOcc 514
  · exact hroot.hOcc 583
  · exact hroot.hOcc 775
  · exact hroot.hOcc 863
  · exact hroot.hOcc 1101
  · exact hroot.hOcc 1103
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1229
  · exact hroot.hOcc 1268
  · exact hroot.hOcc 1284
  · exact hroot.hOcc 1285
  · exact hroot.hOcc 1329
  · exact hroot.hOcc 1330
  · exact hroot.hOcc 1332
  · exact hroot.hOcc 1344
  · exact hroot.hOcc 1404
  · exact hroot.hOcc 1554
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1641
  · exact hroot.hOcc 1656
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (10 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_10

end QiushiMatmul
