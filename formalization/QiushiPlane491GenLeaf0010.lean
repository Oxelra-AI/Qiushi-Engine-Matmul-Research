import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0010Refs : Fin 50 → RowRef 726 49 := ![.occ 79, .occ 81, .occ 119, .occ 128, .occ 144, .occ 188, .occ 220, .occ 221, .occ 237, .occ 284, .occ 285, .occ 287, .occ 320, .occ 341, .occ 377, .occ 493, .occ 494, .occ 506, .occ 509, .occ 510, .occ 513, .occ 516, .occ 552, .occ 559, .occ 573, .occ 594, .occ 628, .occ 631, .occ 647, .occ 651, .occ 654, .occ 691, .occ 698, .occ 701, .occ 702, .occ 724, .occ 725, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchLe 38 (0), .branchGe 6 (1), .branchGe 0 (1), .branchLe 3 (0), .branchLe 47 (0), .branchLe 4 (0)]

def plane491GenLeaf0010Mult : Fin 50 → Nat := ![745182, 214977, 12130, 55061, 391148, 140783, 245761, 592249, 273308, 73323, 62211, 260596, 341041, 125388, 370963, 148820, 165162, 389081, 76125, 190082, 164498, 132168, 96759, 166689, 76457, 258558, 173417, 34912, 299135, 101745, 86338, 309072, 223183, 140666, 117888, 105041, 188613, 1597829, 1409216, 443731, 886916, 549832, 946183, 1230867, 1407747, 1247836, 2943966, 1150152, 1437529, 1233257]

theorem plane491GenLeaf0010 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_0 : (1 : Int) ≤ x 0)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_47 : x 47 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_3 : x 3 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0010Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0010Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0010Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0010Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 119
  · exact hroot.hOcc 128
  · exact hroot.hOcc 144
  · exact hroot.hOcc 188
  · exact hroot.hOcc 220
  · exact hroot.hOcc 221
  · exact hroot.hOcc 237
  · exact hroot.hOcc 284
  · exact hroot.hOcc 285
  · exact hroot.hOcc 287
  · exact hroot.hOcc 320
  · exact hroot.hOcc 341
  · exact hroot.hOcc 377
  · exact hroot.hOcc 493
  · exact hroot.hOcc 494
  · exact hroot.hOcc 506
  · exact hroot.hOcc 509
  · exact hroot.hOcc 510
  · exact hroot.hOcc 513
  · exact hroot.hOcc 516
  · exact hroot.hOcc 552
  · exact hroot.hOcc 559
  · exact hroot.hOcc 573
  · exact hroot.hOcc 594
  · exact hroot.hOcc 628
  · exact hroot.hOcc 631
  · exact hroot.hOcc 647
  · exact hroot.hOcc 651
  · exact hroot.hOcc 654
  · exact hroot.hOcc 691
  · exact hroot.hOcc 698
  · exact hroot.hOcc 701
  · exact hroot.hOcc 702
  · exact hroot.hOcc 724
  · exact hroot.hOcc 725
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (0 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_0
  · change (∑ k, (if k = (3 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_3
  · change (∑ k, (if k = (47 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_47
  · change (∑ k, (if k = (4 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
