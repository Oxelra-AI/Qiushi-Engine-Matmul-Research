import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0105Refs : Fin 50 → RowRef 726 49 := ![.occ 102, .occ 109, .occ 112, .occ 113, .occ 117, .occ 170, .occ 195, .occ 219, .occ 257, .occ 304, .occ 305, .occ 318, .occ 332, .occ 334, .occ 350, .occ 355, .occ 365, .occ 402, .occ 404, .occ 421, .occ 425, .occ 430, .occ 480, .occ 495, .occ 531, .occ 548, .occ 552, .occ 559, .occ 565, .occ 582, .occ 585, .occ 601, .occ 608, .occ 610, .occ 611, .occ 626, .occ 671, .occ 672, .occ 687, .occ 691, .sumGe, .nonneg 16, .nonneg 24, .branchGe 31 (1), .branchGe 44 (1), .branchLe 6 (0), .branchGe 39 (1), .branchLe 27 (0), .branchLe 11 (0), .branchLe 4 (0)]

def plane491GenLeaf0105Mult : Fin 50 → Nat := ![295988, 813705, 884448, 88642, 78608, 68990, 245277, 217066, 133823, 119841, 87069, 170495, 109921, 184258, 6017, 540088, 357321, 40045, 483648, 442344, 382980, 333967, 11148, 294841, 252983, 22296, 168408, 259159, 124417, 143663, 202514, 69052, 121247, 366542, 66329, 20242, 12890, 165600, 361006, 262985, 1342648, 138837, 142159, 1906922, 3509196, 1276319, 1588929, 823687, 1342648, 1047807]

theorem plane491GenLeaf0105 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_44 : (1 : Int) ≤ x 44)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0105Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0105Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0105Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0105Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 102
  · exact hroot.hOcc 109
  · exact hroot.hOcc 112
  · exact hroot.hOcc 113
  · exact hroot.hOcc 117
  · exact hroot.hOcc 170
  · exact hroot.hOcc 195
  · exact hroot.hOcc 219
  · exact hroot.hOcc 257
  · exact hroot.hOcc 304
  · exact hroot.hOcc 305
  · exact hroot.hOcc 318
  · exact hroot.hOcc 332
  · exact hroot.hOcc 334
  · exact hroot.hOcc 350
  · exact hroot.hOcc 355
  · exact hroot.hOcc 365
  · exact hroot.hOcc 402
  · exact hroot.hOcc 404
  · exact hroot.hOcc 421
  · exact hroot.hOcc 425
  · exact hroot.hOcc 430
  · exact hroot.hOcc 480
  · exact hroot.hOcc 495
  · exact hroot.hOcc 531
  · exact hroot.hOcc 548
  · exact hroot.hOcc 552
  · exact hroot.hOcc 559
  · exact hroot.hOcc 565
  · exact hroot.hOcc 582
  · exact hroot.hOcc 585
  · exact hroot.hOcc 601
  · exact hroot.hOcc 608
  · exact hroot.hOcc 610
  · exact hroot.hOcc 611
  · exact hroot.hOcc 626
  · exact hroot.hOcc 671
  · exact hroot.hOcc 672
  · exact hroot.hOcc 687
  · exact hroot.hOcc 691
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (16 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 16
  · change (∑ k, (if k = (24 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 24
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_44
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (39 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (4 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4

end QiushiMatmul
