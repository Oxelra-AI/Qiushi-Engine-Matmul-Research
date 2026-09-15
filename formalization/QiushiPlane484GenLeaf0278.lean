import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0278Refs : Fin 44 → RowRef 1665 43 := ![.occ 84, .occ 119, .occ 123, .occ 125, .occ 128, .occ 136, .occ 141, .occ 216, .occ 230, .occ 309, .occ 788, .occ 861, .occ 1100, .occ 1140, .occ 1143, .occ 1154, .occ 1158, .occ 1180, .occ 1187, .occ 1196, .occ 1205, .occ 1220, .occ 1223, .occ 1248, .occ 1327, .occ 1427, .occ 1471, .occ 1491, .occ 1571, .occ 1608, .occ 1610, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchGe 29 (1), .branchLe 34 (0), .branchLe 13 (0), .branchGe 37 (1), .branchLe 32 (0), .branchGe 8 (1), .branchLe 14 (0)]

def plane484GenLeaf0278Mult : Fin 44 → Nat := ![454, 38, 971, 701, 299, 504, 176, 1312, 1288, 316, 300, 461, 172, 192, 268, 24, 124, 572, 364, 108, 268, 224, 244, 396, 44, 88, 792, 8, 64, 420, 428, 2036, 1644, 1524, 1234, 2036, 1440, 1900, 1704, 604, 2392, 1576, 6078, 1036]

theorem plane484GenLeaf0278 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_8 : (1 : Int) ≤ x 8)
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0278Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0278Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0278Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0278Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 119
  · exact hroot.hOcc 123
  · exact hroot.hOcc 125
  · exact hroot.hOcc 128
  · exact hroot.hOcc 136
  · exact hroot.hOcc 141
  · exact hroot.hOcc 216
  · exact hroot.hOcc 230
  · exact hroot.hOcc 309
  · exact hroot.hOcc 788
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1100
  · exact hroot.hOcc 1140
  · exact hroot.hOcc 1143
  · exact hroot.hOcc 1154
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1180
  · exact hroot.hOcc 1187
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1223
  · exact hroot.hOcc 1248
  · exact hroot.hOcc 1327
  · exact hroot.hOcc 1427
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1571
  · exact hroot.hOcc 1608
  · exact hroot.hOcc 1610
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (8 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_8
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14

end QiushiMatmul
