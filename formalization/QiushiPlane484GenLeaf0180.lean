import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0180Refs : Fin 42 → RowRef 1665 43 := ![.occ 122, .occ 130, .occ 145, .occ 196, .occ 216, .occ 358, .occ 390, .occ 437, .occ 615, .occ 692, .occ 855, .occ 1151, .occ 1160, .occ 1166, .occ 1236, .occ 1241, .occ 1253, .occ 1287, .occ 1299, .occ 1391, .occ 1440, .occ 1491, .occ 1496, .occ 1506, .occ 1562, .occ 1603, .occ 1620, .occ 1651, .occ 1662, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchLe 16 (0), .branchLe 18 (0), .branchLe 1 (0), .branchLe 5 (0), .branchLe 7 (0), .branchLe 14 (0), .branchGe 4 (1), .branchLe 33 (0)]

def plane484GenLeaf0180Mult : Fin 42 → Nat := ![69, 237, 138, 786, 379, 138, 1255, 25, 407, 1082, 582, 444, 36, 149, 294, 587, 273, 747, 15, 407, 679, 298, 12, 924, 73, 601, 429, 295, 440, 2437, 436, 2127, 5937, 5506, 956, 1143, 1629, 2425, 1856, 1331, 4060, 2401]

theorem plane484GenLeaf0180 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_4 : (1 : Int) ≤ x 4)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_14 : x 14 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_33 : x 33 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0180Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0180Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0180Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0180Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 122
  · exact hroot.hOcc 130
  · exact hroot.hOcc 145
  · exact hroot.hOcc 196
  · exact hroot.hOcc 216
  · exact hroot.hOcc 358
  · exact hroot.hOcc 390
  · exact hroot.hOcc 437
  · exact hroot.hOcc 615
  · exact hroot.hOcc 692
  · exact hroot.hOcc 855
  · exact hroot.hOcc 1151
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1241
  · exact hroot.hOcc 1253
  · exact hroot.hOcc 1287
  · exact hroot.hOcc 1299
  · exact hroot.hOcc 1391
  · exact hroot.hOcc 1440
  · exact hroot.hOcc 1491
  · exact hroot.hOcc 1496
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1603
  · exact hroot.hOcc 1620
  · exact hroot.hOcc 1651
  · exact hroot.hOcc 1662
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
  · change (∑ k, (if k = (4 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_4
  · change (∑ k, (if k = (33 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_33

end QiushiMatmul
