import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0513Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 130, .occ 131, .occ 135, .occ 138, .occ 179, .occ 202, .occ 289, .occ 294, .occ 329, .occ 383, .occ 539, .occ 861, .occ 1000, .occ 1116, .occ 1161, .occ 1172, .occ 1173, .occ 1203, .occ 1220, .occ 1234, .occ 1279, .occ 1358, .occ 1467, .occ 1472, .occ 1481, .occ 1483, .occ 1590, .occ 1603, .occ 1610, .occ 1615, .occ 1648, .sumGe, .nonneg 24, .branchGe 15 (1), .branchGe 35 (1), .branchLe 25 (0), .branchLe 26 (0), .branchLe 30 (0), .branchLe 34 (0), .branchLe 8 (0), .branchGe 33 (1), .branchLe 3 (0), .branchGe 0 (1)]

def plane484GenLeaf0513Mult : Fin 44 → Nat := ![947, 827, 5857, 714, 3269, 2651, 4026, 2304, 5611, 347, 356, 102, 1241, 492, 1610, 1978, 477, 4040, 464, 646, 260, 2690, 3158, 3158, 1332, 2014, 2070, 2258, 1223, 1232, 422, 1080, 11451, 1592, 19749, 14776, 9310, 7718, 6765, 11451, 10210, 20653, 4372, 10966]

theorem plane484GenLeaf0513 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_33 : (1 : Int) ≤ x 33)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_30 : x 30 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    (hUB_34 : x 34 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0513Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0513Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0513Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0513Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 130
  · exact hroot.hOcc 131
  · exact hroot.hOcc 135
  · exact hroot.hOcc 138
  · exact hroot.hOcc 179
  · exact hroot.hOcc 202
  · exact hroot.hOcc 289
  · exact hroot.hOcc 294
  · exact hroot.hOcc 329
  · exact hroot.hOcc 383
  · exact hroot.hOcc 539
  · exact hroot.hOcc 861
  · exact hroot.hOcc 1000
  · exact hroot.hOcc 1116
  · exact hroot.hOcc 1161
  · exact hroot.hOcc 1172
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1203
  · exact hroot.hOcc 1220
  · exact hroot.hOcc 1234
  · exact hroot.hOcc 1279
  · exact hroot.hOcc 1358
  · exact hroot.hOcc 1467
  · exact hroot.hOcc 1472
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1590
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1610
  · exact hroot.hOcc 1615
  · exact hroot.hOcc 1648
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (24 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (30 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_30
  · change (∑ k, (if k = (34 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_34
  · change (∑ k, (if k = (8 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (33 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_33
  · change (∑ k, (if k = (3 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (0 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0

end QiushiMatmul
