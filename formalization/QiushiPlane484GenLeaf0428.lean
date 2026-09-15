import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0428Refs : Fin 44 → RowRef 1665 43 := ![.occ 123, .occ 126, .occ 128, .occ 140, .occ 142, .occ 378, .occ 675, .occ 763, .occ 821, .occ 858, .occ 1067, .occ 1110, .occ 1174, .occ 1188, .occ 1191, .occ 1205, .occ 1275, .occ 1282, .occ 1339, .occ 1340, .occ 1375, .occ 1414, .occ 1420, .occ 1460, .occ 1470, .occ 1483, .occ 1484, .occ 1556, .occ 1567, .occ 1609, .occ 1628, .occ 1659, .sumGe, .nonneg 26, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchLe 29 (0), .branchLe 23 (0), .branchLe 19 (0), .branchLe 40 (0), .branchLe 28 (0), .branchLe 4 (0)]

def plane484GenLeaf0428Mult : Fin 44 → Nat := ![1705, 148, 1550, 2187, 1703, 526, 1213, 734, 87, 1259, 171, 136, 256, 2501, 267, 1380, 418, 1044, 797, 757, 311, 1433, 389, 83, 205, 149, 111, 300, 118, 786, 733, 1460, 6394, 1122, 9272, 4454, 4810, 2445, 6165, 6394, 5272, 4878, 5871, 6394]

theorem plane484GenLeaf0428 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_40 : x 40 ≤ (0 : Int))
    (hUB_19 : x 19 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_28 : x 28 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0428Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0428Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0428Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0428Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 123
  · exact hroot.hOcc 126
  · exact hroot.hOcc 128
  · exact hroot.hOcc 140
  · exact hroot.hOcc 142
  · exact hroot.hOcc 378
  · exact hroot.hOcc 675
  · exact hroot.hOcc 763
  · exact hroot.hOcc 821
  · exact hroot.hOcc 858
  · exact hroot.hOcc 1067
  · exact hroot.hOcc 1110
  · exact hroot.hOcc 1174
  · exact hroot.hOcc 1188
  · exact hroot.hOcc 1191
  · exact hroot.hOcc 1205
  · exact hroot.hOcc 1275
  · exact hroot.hOcc 1282
  · exact hroot.hOcc 1339
  · exact hroot.hOcc 1340
  · exact hroot.hOcc 1375
  · exact hroot.hOcc 1414
  · exact hroot.hOcc 1420
  · exact hroot.hOcc 1460
  · exact hroot.hOcc 1470
  · exact hroot.hOcc 1483
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1556
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1609
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1659
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (26 : Fin 43) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 26
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (23 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (19 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_19
  · change (∑ k, (if k = (40 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_40
  · change (∑ k, (if k = (28 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_28
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
