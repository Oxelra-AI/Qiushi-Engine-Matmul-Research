import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0040Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 134, .occ 139, .occ 142, .occ 506, .occ 696, .occ 1092, .occ 1168, .occ 1174, .occ 1213, .occ 1221, .occ 1268, .occ 1278, .occ 1280, .occ 1281, .occ 1282, .occ 1331, .occ 1348, .occ 1379, .occ 1387, .occ 1388, .occ 1412, .occ 1426, .occ 1512, .occ 1564, .occ 1608, .occ 1609, .occ 1618, .occ 1628, .occ 1659, .sumGe, .nonneg 19, .nonneg 22, .nonneg 23, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchGe 25 (1), .branchLe 33 (0), .branchGe 16 (1)]

def plane484GenLeaf0040Mult : Fin 44 → Nat := ![38, 76, 38, 84, 56, 30, 21, 11, 48, 16, 66, 24, 16, 23, 25, 16, 1, 24, 2, 51, 19, 37, 32, 6, 17, 17, 4, 12, 4, 16, 182, 12, 100, 4, 42, 182, 182, 170, 176, 166, 188, 226, 162, 480]

theorem plane484GenLeaf0040 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0040Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0040Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0040Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0040Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 142
  · exact hroot.hOcc 506
  · exact hroot.hOcc 696
  · exact hroot.hOcc 1092
  · exact hroot.hOcc 1168
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1221
  · exact hroot.hOcc 1268
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1280
  · exact hroot.hOcc 1281
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1331
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1379
  · exact hroot.hOcc 1387
  · exact hroot.hOcc 1388
  · exact hroot.hOcc 1412
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1512
  · exact hroot.hOcc 1564
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1618
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (19 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 19
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (23 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 23
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16

end QiushiMatmul
