import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0532Refs : Fin 43 → RowRef 1665 43 := ![.occ 121, .occ 123, .occ 132, .occ 171, .occ 196, .occ 295, .occ 326, .occ 377, .occ 381, .occ 581, .occ 591, .occ 647, .occ 803, .occ 860, .occ 1094, .occ 1205, .occ 1222, .occ 1224, .occ 1228, .occ 1240, .occ 1292, .occ 1300, .occ 1329, .occ 1343, .occ 1358, .occ 1403, .occ 1418, .occ 1597, .occ 1615, .occ 1651, .sumGe, .nonneg 1, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchGe 30 (1), .branchLe 0 (0), .branchLe 19 (0), .branchLe 2 (0), .branchLe 14 (0), .branchLe 40 (0), .branchGe 3 (1)]

def plane484GenLeaf0532Mult : Fin 43 → Nat := ![733, 215, 327, 579, 828, 333, 292, 518, 368, 64, 175, 230, 691, 35, 189, 643, 382, 162, 89, 277, 425, 90, 410, 26, 159, 259, 60, 123, 451, 59, 1461, 196, 2266, 3179, 1167, 1338, 4086, 524, 1338, 1246, 1461, 1461, 3219]

theorem plane484GenLeaf0532 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_3 : (1 : Int) ≤ x 3)
    (hLB_30 : (1 : Int) ≤ x 30)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0532Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0532Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0532Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0532Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 121
  · exact hroot.hOcc 123
  · exact hroot.hOcc 132
  · exact hroot.hOcc 171
  · exact hroot.hOcc 196
  · exact hroot.hOcc 295
  · exact hroot.hOcc 326
  · exact hroot.hOcc 377
  · exact hroot.hOcc 381
  · exact hroot.hOcc 581
  · exact hroot.hOcc 591
  · exact hroot.hOcc 647
  · exact hroot.hOcc 803
  · exact hroot.hOcc 860
  · exact hroot.hOcc 1094
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1224
  · exact hroot.hOcc 1228
  · exact hroot.hOcc 1240
  · exact hroot.hOcc 1292
  · exact hroot.hOcc 1300
  · exact hroot.hOcc 1329
  · exact hroot.hOcc 1343
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1403
  · exact hroot.hOcc 1418
  · exact hroot.hOcc 1597
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1651
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_30
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (14 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_14
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (3 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_3

end QiushiMatmul
