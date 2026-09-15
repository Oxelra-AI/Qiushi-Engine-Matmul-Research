import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0060Refs : Fin 50 → RowRef 726 49 := ![.occ 80, .occ 82, .occ 87, .occ 94, .occ 100, .occ 103, .occ 106, .occ 129, .occ 133, .occ 187, .occ 224, .occ 231, .occ 293, .occ 321, .occ 326, .occ 363, .occ 366, .occ 367, .occ 368, .occ 372, .occ 407, .occ 409, .occ 424, .occ 461, .occ 489, .occ 508, .occ 511, .occ 515, .occ 541, .occ 546, .occ 563, .occ 570, .occ 630, .occ 632, .occ 642, .occ 648, .occ 653, .occ 714, .occ 715, .sumGe, .nonneg 1, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchGe 11 (1), .branchLe 44 (0), .branchLe 46 (0), .branchLe 18 (0), .branchGe 25 (1), .branchLe 0 (0)]

def plane491GenLeaf0060Mult : Fin 50 → Nat := ![2017, 6344, 8197, 6203, 25881, 11454, 19268, 10411, 16616, 2382, 265, 2974, 9500, 1448, 17648, 21, 14336, 1050, 5548, 146, 21956, 1091, 20424, 3145, 15802, 3468, 279, 1230, 11994, 3781, 4723, 9345, 8184, 508, 11880, 2157, 958, 5800, 13074, 44952, 2760, 42795, 31908, 128864, 90805, 43422, 19998, 42764, 31069, 25682]

theorem plane491GenLeaf0060 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_25 : (1 : Int) ≤ x 25)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_18 : x 18 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0060Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0060Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0060Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0060Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 80
  · exact hroot.hOcc 82
  · exact hroot.hOcc 87
  · exact hroot.hOcc 94
  · exact hroot.hOcc 100
  · exact hroot.hOcc 103
  · exact hroot.hOcc 106
  · exact hroot.hOcc 129
  · exact hroot.hOcc 133
  · exact hroot.hOcc 187
  · exact hroot.hOcc 224
  · exact hroot.hOcc 231
  · exact hroot.hOcc 293
  · exact hroot.hOcc 321
  · exact hroot.hOcc 326
  · exact hroot.hOcc 363
  · exact hroot.hOcc 366
  · exact hroot.hOcc 367
  · exact hroot.hOcc 368
  · exact hroot.hOcc 372
  · exact hroot.hOcc 407
  · exact hroot.hOcc 409
  · exact hroot.hOcc 424
  · exact hroot.hOcc 461
  · exact hroot.hOcc 489
  · exact hroot.hOcc 508
  · exact hroot.hOcc 511
  · exact hroot.hOcc 515
  · exact hroot.hOcc 541
  · exact hroot.hOcc 546
  · exact hroot.hOcc 563
  · exact hroot.hOcc 570
  · exact hroot.hOcc 630
  · exact hroot.hOcc 632
  · exact hroot.hOcc 642
  · exact hroot.hOcc 648
  · exact hroot.hOcc 653
  · exact hroot.hOcc 714
  · exact hroot.hOcc 715
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (1 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 1
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (18 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_18
  · change (∑ k, (if k = (25 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_25
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0

end QiushiMatmul
