import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0052Refs : Fin 50 → RowRef 726 49 := ![.occ 100, .occ 104, .occ 108, .occ 114, .occ 115, .occ 119, .occ 150, .occ 161, .occ 219, .occ 254, .occ 256, .occ 277, .occ 299, .occ 312, .occ 323, .occ 324, .occ 338, .occ 382, .occ 394, .occ 401, .occ 416, .occ 424, .occ 425, .occ 511, .occ 526, .occ 539, .occ 548, .occ 568, .occ 569, .occ 580, .occ 594, .occ 632, .occ 639, .occ 642, .occ 653, .occ 669, .occ 691, .occ 714, .occ 724, .sumGe, .nonneg 5, .branchLe 31 (0), .branchLe 16 (0), .branchGe 27 (1), .branchLe 11 (0), .branchLe 23 (0), .branchLe 0 (0), .branchGe 43 (1), .branchLe 48 (0), .branchLe 15 (0)]

def plane491GenLeaf0052Mult : Fin 50 → Nat := ![345224, 29272, 483701, 413882, 168413, 427, 84469, 52915, 62671, 146544, 199663, 21079, 123987, 51087, 57156, 63817, 40474, 29776, 39114, 121053, 238037, 55277, 128061, 127853, 12777, 21338, 47176, 20353, 96713, 98333, 89026, 123871, 7835, 168068, 6023, 30760, 136225, 33035, 30338, 537089, 257073, 350910, 399642, 1085541, 382880, 476262, 307855, 1636562, 265814, 450855]

theorem plane491GenLeaf0052 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_27 : (1 : Int) ≤ x 27)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_48 : x 48 ≤ (0 : Int))
    (hUB_11 : x 11 ≤ (0 : Int))
    (hUB_15 : x 15 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_23 : x 23 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0052Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0052Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0052Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0052Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 100
  · exact hroot.hOcc 104
  · exact hroot.hOcc 108
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 119
  · exact hroot.hOcc 150
  · exact hroot.hOcc 161
  · exact hroot.hOcc 219
  · exact hroot.hOcc 254
  · exact hroot.hOcc 256
  · exact hroot.hOcc 277
  · exact hroot.hOcc 299
  · exact hroot.hOcc 312
  · exact hroot.hOcc 323
  · exact hroot.hOcc 324
  · exact hroot.hOcc 338
  · exact hroot.hOcc 382
  · exact hroot.hOcc 394
  · exact hroot.hOcc 401
  · exact hroot.hOcc 416
  · exact hroot.hOcc 424
  · exact hroot.hOcc 425
  · exact hroot.hOcc 511
  · exact hroot.hOcc 526
  · exact hroot.hOcc 539
  · exact hroot.hOcc 548
  · exact hroot.hOcc 568
  · exact hroot.hOcc 569
  · exact hroot.hOcc 580
  · exact hroot.hOcc 594
  · exact hroot.hOcc 632
  · exact hroot.hOcc 639
  · exact hroot.hOcc 642
  · exact hroot.hOcc 653
  · exact hroot.hOcc 669
  · exact hroot.hOcc 691
  · exact hroot.hOcc 714
  · exact hroot.hOcc 724
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (5 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_27
  · change (∑ k, (if k = (11 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_11
  · change (∑ k, (if k = (23 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_23
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43
  · change (∑ k, (if k = (48 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_48
  · change (∑ k, (if k = (15 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_15

end QiushiMatmul
