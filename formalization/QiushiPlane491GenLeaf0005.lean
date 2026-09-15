import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0005Refs : Fin 50 → RowRef 726 49 := ![.occ 78, .occ 80, .occ 87, .occ 115, .occ 119, .occ 122, .occ 124, .occ 203, .occ 219, .occ 230, .occ 232, .occ 257, .occ 299, .occ 306, .occ 332, .occ 341, .occ 366, .occ 373, .occ 392, .occ 415, .occ 468, .occ 506, .occ 530, .occ 531, .occ 532, .occ 549, .occ 552, .occ 559, .occ 573, .occ 575, .occ 576, .occ 584, .occ 616, .occ 624, .occ 657, .occ 700, .occ 709, .occ 722, .sumGe, .nonneg 34, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchLe 38 (0), .branchLe 6 (0), .branchGe 9 (1), .branchGe 45 (1)]

def plane491GenLeaf0005Mult : Fin 50 → Nat := ![690204, 301583, 13950, 743825, 249010, 120038, 709344, 167705, 139693, 163777, 75154, 481996, 60250, 262900, 44200, 14736, 215417, 8846, 6403, 293599, 110363, 6610, 148598, 12464, 162795, 229465, 391493, 37147, 99136, 193581, 402227, 147560, 21940, 116146, 181188, 50774, 120380, 118347, 1120664, 718962, 394686, 674632, 496163, 733339, 970754, 508897, 951543, 1021528, 2026786, 2759468]

theorem plane491GenLeaf0005 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_45 : (1 : Int) ≤ x 45)
    (hLB_9 : (1 : Int) ≤ x 9)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0005Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0005Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0005Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0005Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 78
  · exact hroot.hOcc 80
  · exact hroot.hOcc 87
  · exact hroot.hOcc 115
  · exact hroot.hOcc 119
  · exact hroot.hOcc 122
  · exact hroot.hOcc 124
  · exact hroot.hOcc 203
  · exact hroot.hOcc 219
  · exact hroot.hOcc 230
  · exact hroot.hOcc 232
  · exact hroot.hOcc 257
  · exact hroot.hOcc 299
  · exact hroot.hOcc 306
  · exact hroot.hOcc 332
  · exact hroot.hOcc 341
  · exact hroot.hOcc 366
  · exact hroot.hOcc 373
  · exact hroot.hOcc 392
  · exact hroot.hOcc 415
  · exact hroot.hOcc 468
  · exact hroot.hOcc 506
  · exact hroot.hOcc 530
  · exact hroot.hOcc 531
  · exact hroot.hOcc 532
  · exact hroot.hOcc 549
  · exact hroot.hOcc 552
  · exact hroot.hOcc 559
  · exact hroot.hOcc 573
  · exact hroot.hOcc 575
  · exact hroot.hOcc 576
  · exact hroot.hOcc 584
  · exact hroot.hOcc 616
  · exact hroot.hOcc 624
  · exact hroot.hOcc 657
  · exact hroot.hOcc 700
  · exact hroot.hOcc 709
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (34 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 34
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (9 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_9
  · change (∑ k, (if k = (45 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_45

end QiushiMatmul
