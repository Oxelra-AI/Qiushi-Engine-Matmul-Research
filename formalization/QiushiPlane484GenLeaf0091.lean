import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0091Refs : Fin 40 → RowRef 1665 43 := ![.occ 121, .occ 122, .occ 125, .occ 128, .occ 130, .occ 131, .occ 135, .occ 136, .occ 179, .occ 352, .occ 649, .occ 651, .occ 804, .occ 850, .occ 911, .occ 1084, .occ 1143, .occ 1145, .occ 1150, .occ 1243, .occ 1246, .occ 1291, .occ 1449, .occ 1478, .occ 1492, .occ 1539, .occ 1546, .occ 1635, .occ 1639, .occ 1663, .sumGe, .nonneg 0, .nonneg 2, .branchLe 15 (0), .branchLe 29 (0), .branchGe 4 (1), .branchLe 36 (0), .branchLe 26 (0), .branchGe 24 (1), .branchLe 18 (0)]

def plane484GenLeaf0091Mult : Fin 40 → Nat := ![65, 432, 203, 65, 1379, 599, 163, 327, 431, 130, 85, 231, 130, 60, 57, 234, 85, 1189, 281, 36, 505, 630, 67, 1031, 130, 18, 232, 411, 227, 536, 2305, 209, 430, 1543, 2175, 6125, 2305, 2078, 2316, 1372]

theorem plane484GenLeaf0091 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_24 : (1 : Int) ≤ x 24)
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0091Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0091Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0091Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0091Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 122
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 135
  · exact hroot.hOcc 136
  · exact hroot.hOcc 179
  · exact hroot.hOcc 352
  · exact hroot.hOcc 649
  · exact hroot.hOcc 651
  · exact hroot.hOcc 804
  · exact hroot.hOcc 850
  · exact hroot.hOcc 911
  · exact hroot.hOcc 1084
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1145
  · exact hroot.hOcc 1150
  · exact hroot.hOcc 1243
  · exact hroot.hOcc 1246
  · exact hroot.hOcc 1291
  · exact hroot.hOcc 1449
  · exact hroot.hOcc 1478
  · exact hroot.hOcc 1492
  · exact hroot.hOcc 1539
  · exact hroot.hOcc 1546
  · exact hroot.hOcc 1635
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1663
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_24
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18

end QiushiMatmul
