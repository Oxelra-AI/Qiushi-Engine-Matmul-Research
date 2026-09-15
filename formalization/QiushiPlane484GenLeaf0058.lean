import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0058Refs : Fin 44 → RowRef 1665 43 := ![.occ 132, .occ 137, .occ 144, .occ 256, .occ 577, .occ 667, .occ 708, .occ 1173, .occ 1177, .occ 1190, .occ 1200, .occ 1213, .occ 1214, .occ 1215, .occ 1305, .occ 1320, .occ 1321, .occ 1322, .occ 1335, .occ 1459, .occ 1510, .occ 1522, .occ 1525, .occ 1530, .occ 1532, .occ 1562, .occ 1617, .occ 1622, .occ 1624, .occ 1626, .occ 1628, .occ 1644, .occ 1650, .sumGe, .branchLe 15 (0), .branchLe 2 (0), .branchLe 29 (0), .branchLe 4 (0), .branchGe 13 (1), .branchLe 42 (0), .branchLe 0 (0), .branchLe 10 (0), .branchLe 20 (0), .branchLe 36 (0)]

def plane484GenLeaf0058Mult : Fin 44 → Nat := ![331234, 282676, 170860, 3802, 17284, 296292, 900992, 517238, 58359, 251766, 205001, 337717, 19610, 179569, 90182, 208652, 115483, 70159, 205614, 734914, 68901, 10567, 58334, 239557, 42205, 115432, 66358, 23142, 85505, 66358, 609877, 760394, 96491, 2207397, 1912896, 707560, 1985076, 2044548, 2881178, 862606, 216570, 2044548, 1809238, 1870126]

theorem plane484GenLeaf0058 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_13 : (1 : Int) ≤ x 13)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_10 : x 10 ≤ (0 : Int))
    (hUB_36 : x 36 ≤ (0 : Int))
    (hUB_42 : x 42 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_20 : x 20 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0058Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0058Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0058Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0058Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 132
  · exact hroot.hOcc 137
  · exact hroot.hOcc 144
  · exact hroot.hOcc 256
  · exact hroot.hOcc 577
  · exact hroot.hOcc 667
  · exact hroot.hOcc 708
  · exact hroot.hOcc 1173
  · exact hroot.hOcc 1177
  · exact hroot.hOcc 1190
  · exact hroot.hOcc 1200
  · exact hroot.hOcc 1213
  · exact hroot.hOcc 1214
  · exact hroot.hOcc 1215
  · exact hroot.hOcc 1305
  · exact hroot.hOcc 1320
  · exact hroot.hOcc 1321
  · exact hroot.hOcc 1322
  · exact hroot.hOcc 1335
  · exact hroot.hOcc 1459
  · exact hroot.hOcc 1510
  · exact hroot.hOcc 1522
  · exact hroot.hOcc 1525
  · exact hroot.hOcc 1530
  · exact hroot.hOcc 1532
  · exact hroot.hOcc 1562
  · exact hroot.hOcc 1617
  · exact hroot.hOcc 1622
  · exact hroot.hOcc 1624
  · exact hroot.hOcc 1626
  · exact hroot.hOcc 1628
  · exact hroot.hOcc 1644
  · exact hroot.hOcc 1650
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15
  · change (∑ k, (if k = (2 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (29 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (4 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (13 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_13
  · change (∑ k, (if k = (42 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_42
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (10 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_10
  · change (∑ k, (if k = (20 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_20
  · change (∑ k, (if k = (36 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_36

end QiushiMatmul
