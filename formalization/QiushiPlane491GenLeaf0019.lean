import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0019Refs : Fin 50 → RowRef 726 49 := ![.occ 83, .occ 88, .occ 94, .occ 103, .occ 112, .occ 121, .occ 145, .occ 180, .occ 219, .occ 220, .occ 248, .occ 254, .occ 257, .occ 281, .occ 306, .occ 324, .occ 353, .occ 382, .occ 409, .occ 410, .occ 425, .occ 429, .occ 432, .occ 433, .occ 506, .occ 508, .occ 511, .occ 549, .occ 570, .occ 576, .occ 594, .occ 628, .occ 647, .occ 685, .occ 700, .occ 711, .occ 714, .occ 725, .sumGe, .nonneg 2, .nonneg 4, .nonneg 5, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchGe 38 (1), .branchGe 1 (1)]

def plane491GenLeaf0019Mult : Fin 50 → Nat := ![85830, 75757, 60564, 18242, 273107, 212002, 211546, 326142, 226818, 35751, 51430, 172481, 82835, 15859, 40272, 13155, 26747, 30082, 64977, 151723, 79192, 22451, 61948, 4922, 72776, 78384, 81469, 12524, 23505, 25211, 222, 151073, 99262, 44499, 22242, 79869, 107042, 41712, 477683, 1694, 31287, 58435, 356102, 260931, 258461, 284676, 331073, 390464, 544392, 1787623]

theorem plane491GenLeaf0019 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_1 : (1 : Int) ≤ x 1)
    (hLB_38 : (1 : Int) ≤ x 38)
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0019Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0019Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0019Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0019Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 83
  · exact hroot.hOcc 88
  · exact hroot.hOcc 94
  · exact hroot.hOcc 103
  · exact hroot.hOcc 112
  · exact hroot.hOcc 121
  · exact hroot.hOcc 145
  · exact hroot.hOcc 180
  · exact hroot.hOcc 219
  · exact hroot.hOcc 220
  · exact hroot.hOcc 248
  · exact hroot.hOcc 254
  · exact hroot.hOcc 257
  · exact hroot.hOcc 281
  · exact hroot.hOcc 306
  · exact hroot.hOcc 324
  · exact hroot.hOcc 353
  · exact hroot.hOcc 382
  · exact hroot.hOcc 409
  · exact hroot.hOcc 410
  · exact hroot.hOcc 425
  · exact hroot.hOcc 429
  · exact hroot.hOcc 432
  · exact hroot.hOcc 433
  · exact hroot.hOcc 506
  · exact hroot.hOcc 508
  · exact hroot.hOcc 511
  · exact hroot.hOcc 549
  · exact hroot.hOcc 570
  · exact hroot.hOcc 576
  · exact hroot.hOcc 594
  · exact hroot.hOcc 628
  · exact hroot.hOcc 647
  · exact hroot.hOcc 685
  · exact hroot.hOcc 700
  · exact hroot.hOcc 711
  · exact hroot.hOcc 714
  · exact hroot.hOcc 725
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (2 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 2
  · change (∑ k, (if k = (4 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 4
  · change (∑ k, (if k = (5 : Fin 49) then (-1 : Int) else 0) * x k) ≤ 0; simpa only [indicator_sum, neg_one_mul, neg_nonpos] using hroot.hNonneg 5
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_38
  · change (∑ k, (if k = (1 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_1

end QiushiMatmul
