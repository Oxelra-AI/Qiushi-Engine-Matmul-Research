import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0214Refs : Fin 44 → RowRef 1665 43 := ![.occ 130, .occ 134, .occ 139, .occ 142, .occ 145, .occ 160, .occ 242, .occ 379, .occ 390, .occ 396, .occ 525, .occ 775, .occ 822, .occ 865, .occ 1160, .occ 1166, .occ 1208, .occ 1214, .occ 1216, .occ 1222, .occ 1227, .occ 1236, .occ 1259, .occ 1284, .occ 1287, .occ 1345, .occ 1348, .occ 1450, .occ 1458, .occ 1471, .occ 1481, .occ 1559, .occ 1662, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchGe 29 (1), .branchGe 35 (1), .branchGe 16 (1), .branchLe 37 (0), .branchLe 22 (0), .branchGe 27 (1), .branchLe 5 (0), .branchLe 20 (0)]

def plane484GenLeaf0214Mult : Fin 44 → Nat := ![2560, 5449, 6618, 12079, 2889, 4402, 4643, 32555, 5137, 1890, 9967, 4924, 18736, 5430, 3077, 5117, 4169, 4817, 5851, 5784, 11475, 9886, 4257, 1401, 4262, 2208, 1730, 3469, 468, 12435, 10277, 5788, 2383, 33956, 19494, 23679, 121188, 81961, 124808, 31573, 14045, 20167, 25761, 18461]

theorem plane484GenLeaf0214 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_16 : (1 : Int) ≤ x 16)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hLB_35 : (1 : Int) ≤ x 35)
    (hUB_37 : x 37 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0214Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0214Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0214Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0214Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 130
  · exact hroot.hOcc 134
  · exact hroot.hOcc 139
  · exact hroot.hOcc 142
  · exact hroot.hOcc 145
  · exact hroot.hOcc 160
  · exact hroot.hOcc 242
  · exact hroot.hOcc 379
  · exact hroot.hOcc 390
  · exact hroot.hOcc 396
  · exact hroot.hOcc 525
  · exact hroot.hOcc 775
  · exact hroot.hOcc 822
  · exact hroot.hOcc 865
  · exact hroot.hOcc 1160
  · exact hroot.hOcc 1166
  · exact hroot.hOcc 1208
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1216
  · exact hroot.hOcc 1222
  · exact hroot.hOcc 1227
  · exact hroot.hOcc 1236
  · exact hroot.hOcc 1259
  · exact hroot.hOcc 1284
  · exact hroot.hOcc 1287
  · exact hroot.hOcc 1345
  · exact hroot.hOcc 1348
  · exact hroot.hOcc 1450
  · exact hroot.hOcc 1458
  · exact hroot.hOcc 1471
  · exact hroot.hOcc 1481
  · exact hroot.hOcc 1559
  · exact hroot.hOcc 1662
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (35 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_35
  · change (∑ k, (if k = (16 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_16
  · change (∑ k, (if k = (37 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_37
  · change (∑ k, (if k = (22 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (27 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20

end QiushiMatmul
