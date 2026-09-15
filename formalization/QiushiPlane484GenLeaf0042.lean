import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0042Refs : Fin 40 → RowRef 1665 43 := ![.occ 99, .occ 125, .occ 132, .occ 159, .occ 164, .occ 1173, .occ 1245, .occ 1269, .occ 1284, .occ 1307, .occ 1308, .occ 1313, .occ 1382, .occ 1390, .occ 1397, .occ 1398, .occ 1428, .occ 1502, .occ 1506, .occ 1509, .occ 1517, .occ 1553, .occ 1562, .occ 1567, .occ 1606, .occ 1626, .occ 1638, .occ 1647, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchLe 13 (0), .branchGe 17 (1), .branchLe 7 (0), .branchLe 18 (0), .branchLe 1 (0), .branchLe 5 (0), .branchLe 16 (0)]

def plane484GenLeaf0042Mult : Fin 40 → Nat := ![3200, 880, 4874, 1194, 338, 1920, 886, 320, 500, 2182, 147, 31, 226, 1355, 1420, 453, 2700, 1385, 1277, 1448, 724, 2129, 1053, 226, 1920, 404, 1044, 876, 9118, 9118, 6092, 8572, 6308, 7198, 16542, 6794, 3840, 9118, 5520, 6972]

theorem plane484GenLeaf0042 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_17 : (1 : Int) ≤ x 17)
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_13 : x 13 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_5 : x 5 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0042Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0042Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0042Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0042Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 99
  · exact hroot.hOcc 125
  · exact hroot.hOcc 132
  · exact hroot.hOcc 159
  · exact hroot.hOcc 164
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1245
  · exact hroot.hOcc 1269
  · exact hroot.hOcc 1284
  · exact hroot.hOcc 1307
  · exact hroot.hOcc 1308
  · exact hroot.hOcc 1313
  · exact hroot.hOcc 1382
  · exact hroot.hOcc 1390
  · exact hroot.hOcc 1397
  · exact hroot.hOcc 1398
  · exact hroot.hOcc 1428
  · exact hroot.hOcc 1502
  · exact hroot.hOcc 1506
  · exact hroot.hOcc 1509
  · exact hroot.hOcc 1517
  · exact hroot.hOcc 1553
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1567
  · exact hroot.hOcc 1606
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1638
  · exact hroot.hOcc 1647
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_13
  · change (∑ k, (if k = (17 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_17
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (18 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1
  · change (∑ k, (if k = (5 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_5
  · change (∑ k, (if k = (16 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16

end QiushiMatmul
