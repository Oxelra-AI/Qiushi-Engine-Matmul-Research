import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0092Refs : Fin 50 → RowRef 726 49 := ![.occ 79, .occ 81, .occ 98, .occ 99, .occ 103, .occ 108, .occ 167, .occ 169, .occ 181, .occ 204, .occ 220, .occ 254, .occ 267, .occ 312, .occ 315, .occ 334, .occ 355, .occ 426, .occ 490, .occ 510, .occ 534, .occ 548, .occ 565, .occ 566, .occ 570, .occ 571, .occ 576, .occ 582, .occ 625, .occ 630, .occ 632, .occ 633, .occ 654, .occ 662, .occ 669, .occ 682, .occ 687, .occ 691, .occ 718, .occ 722, .sumGe, .branchGe 31 (1), .branchLe 44 (0), .branchGe 11 (1), .branchLe 2 (0), .branchLe 7 (0), .branchGe 39 (1), .branchLe 8 (0), .branchLe 27 (0), .branchGe 43 (1)]

def plane491GenLeaf0092Mult : Fin 50 → Nat := ![1176688, 103485, 1130031, 2911846, 621507, 633322, 580126, 254576, 2252379, 669920, 349914, 506098, 385385, 523732, 580405, 1546185, 663939, 1341876, 402195, 11493, 117306, 361336, 670694, 410076, 339836, 415437, 90800, 830355, 567514, 269240, 307168, 49187, 925259, 328451, 192663, 399626, 238924, 323537, 178951, 126659, 3029152, 6737985, 2578956, 9143103, 2317902, 276239, 2806574, 2358458, 2595325, 5818962]

theorem plane491GenLeaf0092 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_11 : (1 : Int) ≤ x 11)
    (hLB_31 : (1 : Int) ≤ x 31)
    (hLB_39 : (1 : Int) ≤ x 39)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_44 : x 44 ≤ (0 : Int))
    (hUB_2 : x 2 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_7 : x 7 ≤ (0 : Int))
    (hUB_8 : x 8 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0092Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0092Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0092Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0092Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 79
  · exact hroot.hOcc 81
  · exact hroot.hOcc 98
  · exact hroot.hOcc 99
  · exact hroot.hOcc 103
  · exact hroot.hOcc 108
  · exact hroot.hOcc 167
  · exact hroot.hOcc 169
  · exact hroot.hOcc 181
  · exact hroot.hOcc 204
  · exact hroot.hOcc 220
  · exact hroot.hOcc 254
  · exact hroot.hOcc 267
  · exact hroot.hOcc 312
  · exact hroot.hOcc 315
  · exact hroot.hOcc 334
  · exact hroot.hOcc 355
  · exact hroot.hOcc 426
  · exact hroot.hOcc 490
  · exact hroot.hOcc 510
  · exact hroot.hOcc 534
  · exact hroot.hOcc 548
  · exact hroot.hOcc 565
  · exact hroot.hOcc 566
  · exact hroot.hOcc 570
  · exact hroot.hOcc 571
  · exact hroot.hOcc 576
  · exact hroot.hOcc 582
  · exact hroot.hOcc 625
  · exact hroot.hOcc 630
  · exact hroot.hOcc 632
  · exact hroot.hOcc 633
  · exact hroot.hOcc 654
  · exact hroot.hOcc 662
  · exact hroot.hOcc 669
  · exact hroot.hOcc 682
  · exact hroot.hOcc 687
  · exact hroot.hOcc 691
  · exact hroot.hOcc 718
  · exact hroot.hOcc 722
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_31
  · change (∑ k, (if k = (44 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_44
  · change (∑ k, (if k = (11 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_11
  · change (∑ k, (if k = (2 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_2
  · change (∑ k, (if k = (7 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_7
  · change (∑ k, (if k = (39 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_39
  · change (∑ k, (if k = (8 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_8
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43

end QiushiMatmul
