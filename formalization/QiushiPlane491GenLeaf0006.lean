import QiushiPlane491GenData
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
namespace QiushiMatmul

def plane491GenLeaf0006Refs : Fin 50 → RowRef 726 49 := ![.occ 82, .occ 105, .occ 107, .occ 115, .occ 122, .occ 126, .occ 230, .occ 248, .occ 255, .occ 258, .occ 273, .occ 287, .occ 293, .occ 297, .occ 332, .occ 335, .occ 351, .occ 365, .occ 367, .occ 377, .occ 384, .occ 410, .occ 414, .occ 432, .occ 486, .occ 487, .occ 511, .occ 559, .occ 563, .occ 590, .occ 642, .occ 647, .occ 651, .occ 653, .occ 685, .occ 707, .occ 716, .sumGe, .branchLe 31 (0), .branchLe 16 (0), .branchLe 27 (0), .branchLe 29 (0), .branchLe 46 (0), .branchLe 32 (0), .branchLe 38 (0), .branchGe 6 (1), .branchLe 0 (0), .branchLe 43 (0), .branchLe 41 (0), .branchLe 9 (0)]

def plane491GenLeaf0006Mult : Fin 50 → Nat := ![472, 7989, 8824, 21680, 3536, 1025, 30018, 11607, 4929, 11608, 9468, 36250, 20991, 17379, 5855, 8760, 14900, 3987, 23398, 23054, 2529, 49983, 38305, 12438, 18455, 16219, 3894, 9468, 10657, 17669, 19395, 35061, 23909, 9679, 4336, 10656, 19833, 120547, 100714, 46310, 46090, 93672, 73762, 101660, 105555, 142809, 120547, 105013, 74829, 45199]

theorem plane491GenLeaf0006 (x : Fin 49 → Int)
    (hroot : plane491GenOccSys.RootHolds x)
    (hLB_6 : (1 : Int) ≤ x 6)
    (hUB_0 : x 0 ≤ (0 : Int))
    (hUB_46 : x 46 ≤ (0 : Int))
    (hUB_9 : x 9 ≤ (0 : Int))
    (hUB_16 : x 16 ≤ (0 : Int))
    (hUB_27 : x 27 ≤ (0 : Int))
    (hUB_29 : x 29 ≤ (0 : Int))
    (hUB_31 : x 31 ≤ (0 : Int))
    (hUB_32 : x 32 ≤ (0 : Int))
    (hUB_38 : x 38 ≤ (0 : Int))
    (hUB_41 : x 41 ≤ (0 : Int))
    (hUB_43 : x 43 ≤ (0 : Int))
    : False := by
  apply farkas_leaf_unsat (fun i j => (plane491GenLeaf0006Refs i).resolveCoeff plane491GenOccSys j)
    (fun i => (plane491GenLeaf0006Refs i).resolveRhs plane491GenOccSys) plane491GenLeaf0006Mult
    (by decide) (by decide) x
  intro i; fin_cases i <;> simp only [plane491GenLeaf0006Refs, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, RowRef.resolveCoeff, RowRef.resolveRhs]
  · exact hroot.hOcc 82
  · exact hroot.hOcc 105
  · exact hroot.hOcc 107
  · exact hroot.hOcc 115
  · exact hroot.hOcc 122
  · exact hroot.hOcc 126
  · exact hroot.hOcc 230
  · exact hroot.hOcc 248
  · exact hroot.hOcc 255
  · exact hroot.hOcc 258
  · exact hroot.hOcc 273
  · exact hroot.hOcc 287
  · exact hroot.hOcc 293
  · exact hroot.hOcc 297
  · exact hroot.hOcc 332
  · exact hroot.hOcc 335
  · exact hroot.hOcc 351
  · exact hroot.hOcc 365
  · exact hroot.hOcc 367
  · exact hroot.hOcc 377
  · exact hroot.hOcc 384
  · exact hroot.hOcc 410
  · exact hroot.hOcc 414
  · exact hroot.hOcc 432
  · exact hroot.hOcc 486
  · exact hroot.hOcc 487
  · exact hroot.hOcc 511
  · exact hroot.hOcc 559
  · exact hroot.hOcc 563
  · exact hroot.hOcc 590
  · exact hroot.hOcc 642
  · exact hroot.hOcc 647
  · exact hroot.hOcc 651
  · exact hroot.hOcc 653
  · exact hroot.hOcc 685
  · exact hroot.hOcc 707
  · exact hroot.hOcc 716
  · change (∑ j, (-1 : Int) * x j) ≤ -plane491GenOccSys.target; simpa only [neg_sum, neg_le_neg_iff] using hroot.hTotal
  · change (∑ k, (if k = (31 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_31
  · change (∑ k, (if k = (16 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_16
  · change (∑ k, (if k = (27 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_27
  · change (∑ k, (if k = (29 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_29
  · change (∑ k, (if k = (46 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_46
  · change (∑ k, (if k = (32 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_32
  · change (∑ k, (if k = (38 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_38
  · change (∑ k, (if k = (6 : Fin 49) then (-1 : Int) else 0) * x k) ≤ -(1 : Int); simpa only [indicator_sum, neg_one_mul, neg_le_neg_iff] using hLB_6
  · change (∑ k, (if k = (0 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_0
  · change (∑ k, (if k = (43 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_43
  · change (∑ k, (if k = (41 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_41
  · change (∑ k, (if k = (9 : Fin 49) then (1 : Int) else 0) * x k) ≤ (0 : Int); simpa only [indicator_sum, one_mul] using hUB_9

end QiushiMatmul
