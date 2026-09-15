import QiushiPlane484GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane484GenLeaf0454Refs : Fin 40 → RowRef 1665 43 := ![.occ 131, .occ 137, .occ 142, .occ 171, .occ 191, .occ 419, .occ 716, .occ 729, .occ 734, .occ 737, .occ 798, .occ 806, .occ 813, .occ 822, .occ 972, .occ 1103, .occ 1302, .occ 1310, .occ 1394, .occ 1402, .occ 1410, .occ 1419, .occ 1431, .occ 1484, .occ 1575, .occ 1619, .occ 1629, .occ 1637, .occ 1656, .occ 1660, .occ 1662, .sumGe, .branchGe 15 (1), .branchLe 35 (0), .branchLe 7 (0), .branchLe 0 (0), .branchGe 29 (1), .branchLe 27 (0), .branchGe 42 (1), .branchLe 1 (0)]

def plane484GenLeaf0454Mult : Fin 40 → Nat := ![29, 42, 94, 34, 123, 12, 323, 281, 13, 101, 21, 34, 102, 3, 13, 2, 13, 12, 29, 177, 8, 71, 87, 137, 26, 43, 63, 181, 29, 28, 32, 386, 880, 217, 378, 158, 1413, 386, 1302, 294]

theorem plane484GenLeaf0454 (x : Fin 43 → Int)
    (hroot : plane484GenOccSys.RootHolds x)
    (hLB_42 : (1 : Int) ≤ x 42)
    (hLB_15 : (1 : Int) ≤ x 15)
    (hLB_29 : (1 : Int) ≤ x 29)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_1 : x 1 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_35 : x 35 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane484GenLeaf0454Refs i).resolveCoeff plane484GenOccSys j)
    (fun i => (plane484GenLeaf0454Refs i).resolveRhs plane484GenOccSys) plane484GenLeaf0454Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane484GenLeaf0454Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 131
  · exact hroot.hOcc 137
  · exact hroot.hOcc 142
  · exact hroot.hOcc 171
  · exact hroot.hOcc 191
  · exact hroot.hOcc 419
  · exact hroot.hOcc 716
  · exact hroot.hOcc 729
  · exact hroot.hOcc 734
  · exact hroot.hOcc 737
  · exact hroot.hOcc 798
  · exact hroot.hOcc 806
  · exact hroot.hOcc 813
  · exact hroot.hOcc 822
  · exact hroot.hOcc 972
  · exact hroot.hOcc 1103
  · exact hroot.hOcc 1302
  · exact hroot.hOcc 1310
  · exact hroot.hOcc 1394
  · exact hroot.hOcc 1402
  · exact hroot.hOcc 1410
  · exact hroot.hOcc 1419
  · exact hroot.hOcc 1431
  · exact hroot.hOcc 1484
  · exact hroot.hOcc 1575
  · exact hroot.hOcc 1619
  · exact hroot.hOcc 1629
  · exact hroot.hOcc 1637
  · exact hroot.hOcc 1656
  · exact hroot.hOcc 1660
  · exact hroot.hOcc 1662
  · change (∑ j, (-1 : Int) * x j) ≤ -plane484GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (15 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_15
  · change (∑ k, (if k = (35 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_35
  · change (∑ k, (if k = (7 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (0 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (29 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_29
  · change (∑ k, (if k = (27 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (42 : Fin 43) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_42
  · change (∑ k, (if k = (1 : Fin 43) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_1

end QiushiMatmul
