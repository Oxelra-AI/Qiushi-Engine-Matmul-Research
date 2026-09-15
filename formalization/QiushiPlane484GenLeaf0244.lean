import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0244Refs : Fin 44 → RowRef 1665 43 := ![.occ 120, .occ 123, .occ 128, .occ 132, .occ 136, .occ 139, .occ 142, .occ 297, .occ 973, .occ 1158, .occ 1174, .occ 1196, .occ 1200, .occ 1221, .occ 1231, .occ 1262, .occ 1264, .occ 1277, .occ 1278, .occ 1331, .occ 1422, .occ 1426, .occ 1470, .occ 1483, .occ 1489, .occ 1554, .occ 1567, .occ 1581, .occ 1602, .occ 1615, .sumGe, .branchLe 15 (0), .branchGe 2 (1), .branchLe 7 (0), .branchLe 23 (0), .branchLe 26 (0), .branchLe 29 (0), .branchLe 17 (0), .branchGe 16 (1), .branchLe 13 (0), .branchLe 41 (0), .branchLe 4 (0), .branchLe 25 (0), .branchLe 11 (0)]

def plane484GenLeaf0244Mult : Fin 44 → Nat := ![2867, 1730, 3830, 439, 7550, 7422, 62, 682, 884, 6837, 1555, 2840, 283, 634, 2388, 522, 1915, 3425, 1989, 7, 810, 1672, 2058, 383, 5282, 390, 922, 1990, 1249, 5401, 16855, 3889, 2135, 12460, 7017, 9371, 15411, 7944, 29535, 13493, 16855, 11454, 2354, 12783]

theorem plane484GenLeaf0244 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_2 : (1 : Int) ≤ x 2)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_17 : x 17 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_25 : x 25 ≤ (0 : Int))
    (hUB_26 : x 26 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0244Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0244Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0244Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0244Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 120
  · exact hroot.hOcc 123
  · exact hroot.hOcc 128
  · exact hroot.hOcc 132
  · exact hroot.hOcc 136
  · exact hroot.hOcc 139
  · exact hroot.hOcc 142
  · exact hroot.hOcc 297
  · exact hroot.hOcc 973
  · exact hroot.hOcc 1158
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1196
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1221
  · exact hroot.hOcc 1231
  · exact hroot.hOcc 1262
  · exact hroot.hOcc 1264
  · exact hroot.hOcc 1277
  · exact hroot.hOcc 1278
  · exact hroot.hOcc 1331
  · exact hroot.hOcc 1422
  · exact hroot.hOcc 1426
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1489
  · exact hroot.hOcc 1554
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1581
  · exact hroot.hOcc 1602
  · exact hroot.hOcc 1615
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_2
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (26 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_26
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (17 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_17
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (41 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (25 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_25
  · change (∑ k, (if k = (11 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11

end QiushiMatmul
