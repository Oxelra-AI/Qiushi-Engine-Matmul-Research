import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0022Refs : Fin 43 → RowRef 1665 43 := ![.occ 128, .occ 134, .occ 140, .occ 142, .occ 210, .occ 284, .occ 564, .occ 658, .occ 829, .occ 1172, .occ 1173, .occ 1221, .occ 1229, .occ 1231, .occ 1243, .occ 1266, .occ 1268, .occ 1278, .occ 1282, .occ 1301, .occ 1303, .occ 1314, .occ 1327, .occ 1331, .occ 1353, .occ 1357, .occ 1597, .occ 1617, .occ 1651, .sumGe, .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchLe 17 (0), .branchGe 35 (1), .branchLe 25 (0), .branchLe 18 (0), .branchLe 42 (0), .branchLe 5 (0), .branchLe 19 (0), .branchLe 7 (0), .branchGe 22 (1)]

def plane484GenLeaf0022Mult : Fin 43 → Nat := ![4902, 1556, 7154, 247, 9386, 1768, 4520, 100, 2113, 2330, 4761, 1795, 251, 672, 529, 5200, 1891, 1019, 96, 1106, 168, 3028, 1635, 3975, 1556, 5627, 2599, 3191, 1501, 17712, 17712, 16156, 12491, 9120, 6029, 22465, 10931, 16156, 17712, 3120, 11683, 14521, 29877]

theorem plane484GenLeaf0022 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_22 : (1 : Int) ≤ x 22)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0022Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0022Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0022Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0022Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 128
  · exact hroot.hOcc 134
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 210
  · exact hroot.hOcc 284
  · exact hroot.hOcc 564
  · exact hroot.hOcc 658
  · exact hroot.hOcc 829
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1221
  · exact hroot.hOcc 1229
  · exact hroot.hOcc 1231
  · exact hroot.hOcc 1243
  · exact hroot.hOcc 1266
  · exact hroot.hOcc 1268
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1301
  · exact hroot.hOcc 1303
  · exact hroot.hOcc 1314
  · exact hroot.hOcc 1327
  · exact hroot.hOcc 1331
  · exact hroot.hOcc 1353
  · exact hroot.hOcc 1357
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1617
  · exact hroot.hOcc 1651
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_22

end QiushiMatmul
