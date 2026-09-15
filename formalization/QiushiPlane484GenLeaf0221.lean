import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0221Refs : Fin 43 → RowRef 1665 43 := ![.occ 119, .occ 121, .occ 132, .occ 139, .occ 141, .occ 201, .occ 242, .occ 323, .occ 379, .occ 386, .occ 437, .occ 556, .occ 591, .occ 594, .occ 673, .occ 1080, .occ 1159, .occ 1160, .occ 1190, .occ 1191, .occ 1206, .occ 1222, .occ 1236, .occ 1258, .occ 1262, .occ 1370, .occ 1425, .occ 1471, .occ 1610, .occ 1638, .occ 1639, .occ 1662, .sumGe, .nonneg 22, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchGe 16 (1), .branchGe 37 (1), .branchGe 17 (1), .branchLe 20 (0), .branchLe 32 (0)]

def plane484GenLeaf0221Mult : Fin 43 → Nat := ![844, 562, 314, 1364, 314, 38, 1234, 3122, 1936, 1010, 1630, 1314, 338, 378, 968, 324, 843, 38, 216, 932, 531, 114, 1054, 700, 116, 46, 1176, 703, 381, 428, 46, 426, 3160, 46, 1360, 528, 10016, 11418, 9880, 3048, 5518, 1676, 3160]

theorem plane484GenLeaf0221 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_37 : (1 : Int) ≤ x 37)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0221Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0221Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0221Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0221Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 119
  · exact hroot.hOcc 121
  · exact hroot.hOcc 132
  · exact hroot.hOcc 139
  · exact hroot.hOcc 141
  · exact hroot.hOcc 201
  · exact hroot.hOcc 242
  · exact hroot.hOcc 323
  · exact hroot.hOcc 379
  · exact hroot.hOcc 386
  · exact hroot.hOcc 437
  · exact hroot.hOcc 556
  · exact hroot.hOcc 591
  · exact hroot.hOcc 594
  · exact hroot.hOcc 673
  · exact hroot.hOcc 1080
  · exact hroot.hOcc 1159
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1206
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1258
  · exact hroot.hOcc 1262
  · exact hroot.hOcc 1370
  · exact hroot.hOcc 1425
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1639
  · exact hroot.hOcc 1662
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (22 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 22
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (37 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_37
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (32 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32

end QiushiMatmul
