import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0001Refs : Fin 50 → RowRef 726 49 := ![.occ 88, .occ 107, .occ 108, .occ 114, .occ 115, .occ 123, .occ 231, .occ 254, .occ 256, .occ 257, .occ 258, .occ 287, .occ 293, .occ 320, .occ 324, .occ 326, .occ 331, .occ 358, .occ 373, .occ 379, .occ 382, .occ 450, .occ 532, .occ 541, .occ 543, .occ 563, .occ 566, .occ 576, .occ 586, .occ 643, .occ 651, .occ 653, .occ 668, .occ 670, .occ 671, .occ 716, .occ 724, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchLe 38 (0), .branchLe 6 (0), .branchLe 9 (0), .branchLe 4 (0), .branchLe 0 (0), .branchGe 43 (1)]

def plane491GenLeaf0001Mult : Fin 50 → Nat := ![963476, 1225587, 2223818, 2256698, 734854, 1250529, 328870, 986301, 701766, 713213, 235360, 204283, 343498, 702973, 844446, 773925, 625133, 360414, 845844, 200195, 363879, 209622, 105266, 922950, 531736, 144437, 97232, 508708, 442875, 391212, 136277, 610732, 542935, 121686, 19445, 425051, 1210060, 3898855, 3357127, 2214495, 730062, 3898855, 2563830, 2157059, 3507643, 3151846, 3569985, 1451325, 2583529, 8445737]

theorem plane491GenLeaf0001 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_43 : (1 : Int) ≤ x 43)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_4 : x 4 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_6 : x 6 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0001Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0001Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0001Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0001Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 88
  · exact hroot.hOcc 107
  · exact hroot.hOcc 108
  · exact hroot.hOcc 114
  · exact hroot.hOcc 115
  · exact hroot.hOcc 123
  · exact hroot.hOcc 231
  · exact hroot.hOcc 254
  · exact hroot.hOcc 256
  · exact hroot.hOcc 257
  · exact hroot.hOcc 258
  · exact hroot.hOcc 287
  · exact hroot.hOcc 293
  · exact hroot.hOcc 320
  · exact hroot.hOcc 324
  · exact hroot.hOcc 326
  · exact hroot.hOcc 331
  · exact hroot.hOcc 358
  · exact hroot.hOcc 373
  · exact hroot.hOcc 379
  · exact hroot.hOcc 382
  · exact hroot.hOcc 450
  · exact hroot.hOcc 532
  · exact hroot.hOcc 541
  · exact hroot.hOcc 543
  · exact hroot.hOcc 563
  · exact hroot.hOcc 566
  · exact hroot.hOcc 576
  · exact hroot.hOcc 586
  · exact hroot.hOcc 643
  · exact hroot.hOcc 651
  · exact hroot.hOcc 653
  · exact hroot.hOcc 668
  · exact hroot.hOcc 670
  · exact hroot.hOcc 671
  · exact hroot.hOcc 716
  · exact hroot.hOcc 724
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (6 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_6
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9
  · change (∑ k, (if k = (4 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_4
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (43 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_43

end QiushiMatmul
