import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0178Refs : Fin 44 → RowRef 1665 43 := ![.occ 132, .occ 216, .occ 248, .occ 316, .occ 389, .occ 390, .occ 404, .occ 437, .occ 470, .occ 1164, .occ 1173, .occ 1214, .occ 1216, .occ 1220, .occ 1227, .occ 1253, .occ 1259, .occ 1283, .occ 1328, .occ 1353, .occ 1413, .occ 1417, .occ 1427, .occ 1430, .occ 1486, .occ 1488, .occ 1501, .occ 1561, .occ 1562, .occ 1603, .occ 1606, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchLe 1 (0), .branchLe 5 (0), .branchLe 7 (0), .branchLe 14 (0), .branchLe 4 (0), .branchLe 6 (0)]

def plane484GenLeaf0178Mult : Fin 44 → Nat := ![440, 8821, 156, 1144, 3516, 478, 1082, 9202, 11353, 125, 176, 5183, 6985, 2762, 4546, 792, 1947, 426, 2361, 3964, 1800, 3185, 1925, 704, 6253, 585, 284, 5035, 434, 2649, 528, 17629, 14444, 10791, 60060, 50388, 15268, 16485, 12446, 15682, 9304, 17453, 16837, 14558]

theorem plane484GenLeaf0178 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0178Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0178Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0178Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0178Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 132
  · exact hroot.hOcc 216
  · exact hroot.hOcc 248
  · exact hroot.hOcc 316
  · exact hroot.hOcc 389
  · exact hroot.hOcc 390
  · exact hroot.hOcc 404
  · exact hroot.hOcc 437
  · exact hroot.hOcc 470
  · exact hroot.hOcc 1164
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1227
  · exact hroot.hOcc 1253
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1283
  · exact hroot.hOcc 1328
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1413
  · exact hroot.hOcc 1417
  · exact hroot.hOcc 1427
  · exact hroot.hOcc 1430
  · exact hroot.hOcc 1486
  · exact hroot.hOcc 1488
  · exact hroot.hOcc 1501
  · exact hroot.hOcc 1561
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1606
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (6 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6

end QiushiMatmul
