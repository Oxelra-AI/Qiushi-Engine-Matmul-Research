import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0024Refs : Fin 50 → RowRef 726 49 := ![.occ 84, .occ 99, .occ 100, .occ 102, .occ 114, .occ 174, .occ 221, .occ 237, .occ 242, .occ 243, .occ 244, .occ 257, .occ 273, .occ 287, .occ 303, .occ 305, .occ 331, .occ 351, .occ 367, .occ 372, .occ 382, .occ 399, .occ 402, .occ 409, .occ 423, .occ 431, .occ 492, .occ 494, .occ 517, .occ 536, .occ 552, .occ 568, .occ 584, .occ 590, .occ 594, .occ 621, .occ 628, .occ 685, .occ 700, .sumGe, .nonneg 0, .nonneg 14, .branchLe 31 (0), .branchLe 16 (0), .branchLe 29 (0), .branchLe 46 (0), .branchGe 32 (1), .branchGe 28 (1), .branchLe 22 (0), .branchGe 7 (1)]

def plane491GenLeaf0024Mult : Fin 50 → Nat := ![91, 6882, 14795, 8762, 6777, 15880, 9388, 6507, 9208, 3910, 167, 1139, 6007, 4138, 1197, 987, 12001, 10641, 592, 929, 2356, 1713, 2, 285, 1122, 1046, 817, 5285, 2812, 2850, 4111, 4030, 3553, 2055, 31, 2748, 10647, 1347, 4453, 21982, 6387, 1866, 15198, 6539, 11302, 16180, 64522, 65115, 16036, 60185]

theorem plane491GenLeaf0024 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_28 : (1 : Int) ≤ x 28)
    (hLB_32 : (1 : Int) ≤ x 32)
    (hLB_7 : (1 : Int) ≤ x 7)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_22 : x 22 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0024Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0024Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0024Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0024Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 84
  · exact hroot.hOcc 99
  · exact hroot.hOcc 100
  · exact hroot.hOcc 102
  · exact hroot.hOcc 114
  · exact hroot.hOcc 174
  · exact hroot.hOcc 221
  · exact hroot.hOcc 237
  · exact hroot.hOcc 242
  · exact hroot.hOcc 243
  · exact hroot.hOcc 244
  · exact hroot.hOcc 257
  · exact hroot.hOcc 273
  · exact hroot.hOcc 287
  · exact hroot.hOcc 303
  · exact hroot.hOcc 305
  · exact hroot.hOcc 331
  · exact hroot.hOcc 351
  · exact hroot.hOcc 367
  · exact hroot.hOcc 372
  · exact hroot.hOcc 382
  · exact hroot.hOcc 399
  · exact hroot.hOcc 402
  · exact hroot.hOcc 409
  · exact hroot.hOcc 423
  · exact hroot.hOcc 431
  · exact hroot.hOcc 492
  · exact hroot.hOcc 494
  · exact hroot.hOcc 517
  · exact hroot.hOcc 536
  · exact hroot.hOcc 552
  · exact hroot.hOcc 568
  · exact hroot.hOcc 584
  · exact hroot.hOcc 590
  · exact hroot.hOcc 594
  · exact hroot.hOcc 621
  · exact hroot.hOcc 628
  · exact hroot.hOcc 685
  · exact hroot.hOcc 700
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (0 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 0
  · change (∑ k, (if k = (14 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 14
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_32
  · change (∑ k, (if k = (28 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_28
  · change (∑ k, (if k = (22 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_22
  · change (∑ k, (if k = (7 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_7

end QiushiMatmul
